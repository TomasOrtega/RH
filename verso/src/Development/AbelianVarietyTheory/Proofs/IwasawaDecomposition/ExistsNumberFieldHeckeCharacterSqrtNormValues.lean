import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisGe

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.BVal

open Formalism.L2.Host
open scoped nonZeroDivisors

section General

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Establish `hf : ∀ K : FractionalIdeal (𝓞 L)⁰ L, (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v K).Finite` using `fun K => by`. Use `(FractionalIdeal.finite_factors (K := L) K).subset fun v hv h => hv ?_` and prove the remaining obligations. Establish `h' : FractionalIdeal.count L v K = 0` using `h`. Simplify using `[h']`. Unfold `HChar.onId`.

Rewrite using `[← finprod_mul_distrib (hf I) (hf J)]`. Use `finprod_congr fun v => ?_` and prove the remaining obligations. Rewrite using `[FractionalIdeal.count_mul L v hI hJ, _root_.zpow_add]`.
-/
theorem onId_mul (χ : HChar L) {I J : FractionalIdeal (𝓞 L)⁰ L} (hI : I ≠ 0) (hJ : J ≠ 0) :
    χ.onId (I * J) = χ.onId I * χ.onId J := by
  have hf : ∀ K : FractionalIdeal (𝓞 L)⁰ L,
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v K).Finite := fun K => by
    refine (FractionalIdeal.finite_factors (K := L) K).subset fun v hv h => hv ?_
    have h' : FractionalIdeal.count L v K = 0 := h
    simp [h']
  unfold HChar.onId
  rw [← finprod_mul_distrib (hf I) (hf J)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_mul L v hI hJ, _root_.zpow_add]

/- English proof (translation)
Unfold `HChar.onId`. Simplify using `[FractionalIdeal.count_one]`.
-/
theorem onId_one (χ : HChar L) : χ.onId 1 = 1 := by
  unfold HChar.onId
  simp [FractionalIdeal.count_one]

/- English proof (translation)
Unfold `HChar.onId`. Rewrite using `[finprod_eq_single _ v fun w hw => by rw [FractionalIdeal.count_maximal_coprime L w hw.symm, zpow_zero], FractionalIdeal.count_self, zpow_one]`.
-/
theorem onId_prime (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    χ.onId (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := by
  unfold HChar.onId
  rw [finprod_eq_single _ v fun w hw => by rw [FractionalIdeal.count_maximal_coprime L w hw.symm, zpow_zero],
    FractionalIdeal.count_self, zpow_one]

/- English proof (translation)
Proceed by induction on `cc using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => exact absurd rfl h0`. Consider the case `h₂ x hx`. Take `rfl : x = ⊤` from `Ideal.isUnit_iff.1 hx`. Simplify using `[onId_one]`.

Consider the case `h₃ a p ha hp ih`. Set `v : HeightOneSpectrum (𝓞 L)` to `⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩`. Establish `hb : b ∉ v.asIdeal` using `fun hb => v.isPrime.ne_top (top_le_iff.1 (h1.ge.trans (sup_le Ideal.mul_le_left ((Ideal.span_singleton_le_iff_mem _).2 hb))))`. Establish `ha1 : a ⊔ Ideal.span {b} = ⊤` using `top_le_iff.1 (h1.ge.trans (sup_le_sup_right Ideal.mul_le_right _))`. Use `mul_mem (h v hb) (ih ha ha1)` as an intermediate fact.

Rewrite using `[FractionalIdeal.coeIdeal_mul, onId_mul χ (FractionalIdeal.coeIdeal_ne_zero.2 hp.ne_zero) (FractionalIdeal.coeIdeal_ne_zero.2 ha), map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), show χ.onId (p : FractionalIdeal (𝓞 L)⁰ L) = χ.val v from onId_prime χ v]`. Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_of_primes (χ : HChar L) (M : IntermediateField ℚ ℂ) (b : 𝓞 L)
    (h : ∀ v : HeightOneSpectrum (𝓞 L), b ∉ v.asIdeal →
      ((χ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M)
    (cc : Ideal (𝓞 L)) (h0 : cc ≠ ⊥) (h1 : cc ⊔ Ideal.span {b} = ⊤) :
    ((χ.onId (cc : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) ∈ M := by
  induction cc using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h0
  | h₂ x hx =>
    obtain rfl : x = ⊤ := Ideal.isUnit_iff.1 hx
    simp [onId_one]
  | h₃ a p ha hp ih =>
    let v : HeightOneSpectrum (𝓞 L) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hb : b ∉ v.asIdeal := fun hb => v.isPrime.ne_top
      (top_le_iff.1 (h1.ge.trans (sup_le Ideal.mul_le_left ((Ideal.span_singleton_le_iff_mem _).2 hb))))
    have ha1 : a ⊔ Ideal.span {b} = ⊤ := top_le_iff.1 (h1.ge.trans (sup_le_sup_right Ideal.mul_le_right _))
    have := mul_mem (h v hb) (ih ha ha1)
    rw [FractionalIdeal.coeIdeal_mul, onId_mul χ (FractionalIdeal.coeIdeal_ne_zero.2 hp.ne_zero)
      (FractionalIdeal.coeIdeal_ne_zero.2 ha), map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
      show χ.onId (p : FractionalIdeal (𝓞 L)⁰ L) = χ.val v from onId_prime χ v]
    convert this using 1
    push_cast
    ring

/- English proof (translation)
Establish `e : (α * β * γ⁻¹).val v = α.val v * β.val v * (γ.val v)⁻¹` using `rfl`. Establish `e2 : ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ (((1 / 2 : ℝ)) : ℂ)`. Rewrite using `[Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]`. Rewrite using `[e, e2]`. Simplify using `only [HChar.valTw, Complex.cpow_neg, Complex.ofReal_zero, Complex.cpow_zero, inv_one, mul_one, mul_inv, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc]`.
-/
theorem val_mul_sqrt (α β γ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    (((α * β * γ⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) =
      α.valTw 0 v * β.valTw 0 v * (γ.valTw (1 / 2) v)⁻¹ := by
  have e : (α * β * γ⁻¹).val v = α.val v * β.val v * (γ.val v)⁻¹ := rfl
  have e2 : ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]
  rw [e, e2]
  simp only [HChar.valTw, Complex.cpow_neg, Complex.ofReal_zero, Complex.cpow_zero, inv_one, mul_one, mul_inv, inv_inv,
    Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc]

end General

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R hL i t`. Take `⟨M₁, hM₁, -, -, hmu, heta, -⟩` from `GlobalTheory.Mem.FrameVal.frame_values D.R D.host (eExp D) ⟨R.C.P, R.C.W, R.C.mu0, R.C.eta, R.C.chiPsi, R.C.del, R.C.del', R.C.isMu0, R.C.isEta, R.C.isChi, R.C.isDel, R.C.isDel'⟩ fun j τ => (D.hc _).e_int j`. Take `⟨M₂, hM₂, hxi⟩` from `GlobalTheory.Mem.FrameVal.exists_of_order (hL.xi_fin t)`. Use `⟨M₁ ⊔ M₂, inferInstance, fun M' hM bad hg hQ => ?_⟩` and prove the remaining obligations. Establish `key : ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal → (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M'`.

Introduce `v hv`. Establish `u1 : (R.C.mu0 i).UnrAt v` using `(R.C.isMu0 i).unr v fun k hk => hv (by`. Establish `hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal` using `hk`. Establish `hd : D.host.g k ∣ bad`. Use `dvd_trans ?_ hg` and prove the remaining obligations.

Use `fin_cases k`. Conclude with `dvd_mul_right _ _`. Conclude with `dvd_mul_left _ _`. Take `⟨c, rfl⟩` from `hd`. Rewrite using `[Nat.cast_mul]`.

Conclude with `Ideal.mul_mem_right _ _ hk')`. Establish `u2 : (R.xiH t).UnrAt v`. Assume the negation of the conclusion as `h`. Break down `(hL.Q_ram t v).1 h with h | ⟨P', hP', h⟩` into its components or cases. Conclude with `hv (hQ v h)`.

Take `⟨c', hc', e⟩` from `h _ (hQ P' hP')`. Establish `e' : c' = (bad : 𝓞 D.host.E)` using `RingOfIntegers.ext (by`. Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `star ((bad : 𝓞 D.host.E) : D.host.E) = ((bad : 𝓞 D.host.E) : D.host.E)`. Rewrite using `[show ((bad : 𝓞 D.host.E) : D.host.E) = (bad : D.host.E) from map_natCast (algebraMap (𝓞 D.host.E) D.host.E) bad, star_natCast])`.

Conclude with `hv (e' ▸ hc')`. Take `⟨y1, hy1⟩` from `hmu i v u1`. Take `⟨y2, hy2⟩` from `hxi v u2`. Take `⟨y3, hy3⟩` from `heta v (R.C.isEta.unr v)`. Rewrite using `[val_mul_sqrt, ← hy1, ← hy2, ← hy3]`.

Conclude with `mul_mem (mul_mem (hM (le_sup_left (b := M₂) y1.2)) (hM (le_sup_right (a := M₁) y2.2))) (inv_mem (hM (le_sup_left (b := M₂) y3.2)))`. Use `⟨fun cc => if h : cc ≠ ⊥ ∧ cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ then ⟨_, mem_of_primes _ M' _ key cc h.1 h.2⟩ else 0, fun cc h0 h1 => ?_⟩` and prove the remaining obligations. Simplify using `only [dif_pos (And.intro h0 h1)]`. Both sides reduce to the same expression.
-/
theorem exists_field_BIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T0), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ (M' : IntermediateField ℚ ℂ), M ≤ M' → ∀ bad : ℕ, D.host.g 0 * D.host.g 1 ∣ bad → (∀ PP ∈ R.Q t, ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ B : Ideal (𝓞 D.host.E) → M', BIs R i M'.val.toRingHom t bad B := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL i t
  obtain ⟨M₁, hM₁, -, -, hmu, heta, -⟩ := GlobalTheory.Mem.FrameVal.frame_values D.R D.host (eExp D)
    ⟨R.C.P, R.C.W, R.C.mu0, R.C.eta, R.C.chiPsi, R.C.del, R.C.del', R.C.isMu0, R.C.isEta, R.C.isChi, R.C.isDel, R.C.isDel'⟩
    fun j τ => (D.hc _).e_int j
  obtain ⟨M₂, hM₂, hxi⟩ := GlobalTheory.Mem.FrameVal.exists_of_order (hL.xi_fin t)
  refine ⟨M₁ ⊔ M₂, inferInstance, fun M' hM bad hg hQ => ?_⟩
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal →
      (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M' := by
    intro v hv
    have u1 : (R.C.mu0 i).UnrAt v := (R.C.isMu0 i).unr v fun k hk => hv (by
      have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := hk
      have hd : D.host.g k ∣ bad := by
        refine dvd_trans ?_ hg
        fin_cases k
        · exact dvd_mul_right _ _
        · exact dvd_mul_left _ _
      obtain ⟨c, rfl⟩ := hd
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hk')
    have u2 : (R.xiH t).UnrAt v := by
      by_contra h
      rcases (hL.Q_ram t v).1 h with h | ⟨P', hP', h⟩
      · exact hv (hQ v h)
      · obtain ⟨c', hc', e⟩ := h _ (hQ P' hP')
        have e' : c' = (bad : 𝓞 D.host.E) := RingOfIntegers.ext (by
          rw [e]
          change star ((bad : 𝓞 D.host.E) : D.host.E) = ((bad : 𝓞 D.host.E) : D.host.E)
          rw [show ((bad : 𝓞 D.host.E) : D.host.E) = (bad : D.host.E) from
            map_natCast (algebraMap (𝓞 D.host.E) D.host.E) bad, star_natCast])
        exact hv (e' ▸ hc')
    obtain ⟨y1, hy1⟩ := hmu i v u1
    obtain ⟨y2, hy2⟩ := hxi v u2
    obtain ⟨y3, hy3⟩ := heta v (R.C.isEta.unr v)
    rw [val_mul_sqrt, ← hy1, ← hy2, ← hy3]
    exact mul_mem (mul_mem (hM (le_sup_left (b := M₂) y1.2)) (hM (le_sup_right (a := M₁) y2.2)))
      (inv_mem (hM (le_sup_left (b := M₂) y3.2)))
  classical
  refine ⟨fun cc => if h : cc ≠ ⊥ ∧ cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ then
    ⟨_, mem_of_primes _ M' _ key cc h.1 h.2⟩ else 0, fun cc h0 h1 => ?_⟩
  simp only [dif_pos (And.intro h0 h1)]
  rfl

end GlobalTheory.Mem.BVal
