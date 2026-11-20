import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

noncomputable section

namespace GlobalTheory.SeeSaw.TwLev.GlueApprox

section Local

variable {k Γ : Type} [Field k] [LinearOrderedCommGroupWithZero Γ] {v : Valuation k Γ} {n : ℕ}

/- English proof (translation)
Establish `hB : ColAd.Sm v 1 B` using `fun i j => by`. Use `ColAd.int_of_mulVec h hγ (x := fun l => B l j) (fun l => ?_) i` and prove the remaining obligations. Establish `e : (A *ᵥ fun l => B l j) l = (A * B) l j` using `rfl`. Rewrite using `[e, hAB, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hBA : B * A = 1` using `mul_eq_one_comm.1 hAB`. Establish `e : B - 1 = -(B * (A - 1))` using `by rw [Matrix.mul_sub, hBA, Matrix.mul_one]; abel`. Introduce `i j`. Rewrite using `[e, Matrix.neg_apply, Valuation.map_neg]`. Use `hB.mul h i j` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem sm_inv_sub_one {γ : Γ} (hγ : γ < 1) {A B : Matrix (Fin n) (Fin n) k} (h : ColAd.Sm v γ (A - 1))
    (hAB : A * B = 1) : ColAd.Sm v γ (B - 1) := by
  have hB : ColAd.Sm v 1 B := fun i j => by
    refine ColAd.int_of_mulVec h hγ (x := fun l => B l j) (fun l => ?_) i
    have e : (A *ᵥ fun l => B l j) l = (A * B) l j := rfl
    rw [e, hAB, Matrix.one_apply]
    split_ifs <;> simp
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  have e : B - 1 = -(B * (A - 1)) := by rw [Matrix.mul_sub, hBA, Matrix.mul_one]; abel
  intro i j
  rw [e, Matrix.neg_apply, Valuation.map_neg]
  have := hB.mul h i j
  rwa [one_mul] at this

end Local

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Introduce `hd`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hd`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hw0`. Use `replace hi : w i ≠ 0 := hi`. Use `set c : E := (a * w i)⁻¹ with hc`.

Set `x : Fin n → P.adicCompletion E` to `fun l => algebraMap E _ ((c • w) l)`. Establish `hx0 : C.map (algebraMap E (P.adicCompletion E)) *ᵥ x = 0`. Use function extensionality and compare the values at `l`. Rewrite using `[Pi.zero_apply, show x = (algebraMap E (P.adicCompletion E)) ∘ (c • w) from rfl, ← RingHom.map_mulVec, Matrix.mulVec_smul, hw, smul_zero, Pi.zero_apply, map_zero]`. Establish `h4` using `ColAd.int_of_mulVec h hγ (x := x) (fun l => by`.

Rewrite using `[← Matrix.mulVec_mulVec, hx0, Matrix.mulVec_zero, Pi.zero_apply, map_zero]`. Conclude with `zero_le_one) i`. Establish `e : (c • w) i = a⁻¹`. Rewrite using `[Pi.smul_apply, smul_eq_mul, hc]`. Clear the denominators using the available nonvanishing facts.

Establish `ha0' : P.valuation E a ≠ 0` using `(Valuation.ne_zero_iff _).2 ha0`. Simplify using `only [x] at h4`. Rewrite `h4` using `[e, valued_algebraMap, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ha0')]`. Conclude with `absurd ha (not_lt.2 h4)`.
-/
theorem det_ne_zero_of_sm {P : HeightOneSpectrum (𝓞 E)} {γ : WithZero (Multiplicative ℤ)} (hγ : γ < 1) {a : E}
    (ha0 : a ≠ 0) (ha : P.valuation E a < 1) (Zi : Matrix (Fin n) (Fin n) (P.adicCompletion E))
    (C : Matrix (Fin n) (Fin n) E) (h : ColAd.Sm Valued.v γ (Zi * C.map (algebraMap E _) - 1)) : C.det ≠ 0 := by
  intro hd
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw0
  replace hi : w i ≠ 0 := hi
  set c : E := (a * w i)⁻¹ with hc
  let x : Fin n → P.adicCompletion E := fun l => algebraMap E _ ((c • w) l)
  have hx0 : C.map (algebraMap E (P.adicCompletion E)) *ᵥ x = 0 := by
    funext l
    rw [Pi.zero_apply, show x = (algebraMap E (P.adicCompletion E)) ∘ (c • w) from rfl, ← RingHom.map_mulVec,
      Matrix.mulVec_smul, hw, smul_zero, Pi.zero_apply, map_zero]
  have h4 := ColAd.int_of_mulVec h hγ (x := x) (fun l => by
    rw [← Matrix.mulVec_mulVec, hx0, Matrix.mulVec_zero, Pi.zero_apply, map_zero]
    exact zero_le_one) i
  have e : (c • w) i = a⁻¹ := by
    rw [Pi.smul_apply, smul_eq_mul, hc]
    field_simp
  have ha0' : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
  simp only [x] at h4
  rw [e, valued_algebraMap, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ha0')] at h4
  exact absurd ha (not_lt.2 h4)

/- English proof (translation)
Take `⟨y, N, r, hr, hN, e⟩` from `exists_approx_small x {P} hγ`. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[e, map_add, adAt_inclE, add_sub_cancel_left]`. Conclude with `valued_nat_mul_lt hr (hN P (by simp))`.
-/
theorem exists_near_entry (x : AfE F E) (P : HeightOneSpectrum (𝓞 E)) {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0) :
    ∃ y : E, Valued.v (adAt F P x - algebraMap E _ y) < γ := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small x {P} hγ
  refine ⟨y, ?_⟩
  rw [e, map_add, adAt_inclE, add_sub_cancel_left]
  exact valued_nat_mul_lt hr (hN P (by simp))

/- English proof (translation)
Rewrite using `[map_sub, ← ColAd.locM_one (F := F) (P := w)]`. Both sides reduce to the same expression.
-/
theorem locM_sub_one_apply (w : HeightOneSpectrum (𝓞 E)) (x : GL (Fin n) (AfE F E)) (i j : Fin n) :
    (ColAd.locM w x - 1) i j =
      adAt F w ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  rw [map_sub, ← ColAd.locM_one (F := F) (P := w)]
  rfl

variable [StarRing E] (hc : CMData F E)

local notation "ι" => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
local notation "σ" => Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F)

/- English proof (translation)
Rewrite using `[PtExist.inv_apply hu, map_sub]`. Use `congr 1`. Break down `eq_or_ne i j with rfl | h` into its components or cases. Rewrite using `[Matrix.one_apply_eq, map_one]`. Rewrite using `[Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm, map_zero]`.
-/
theorem inv_sub_one_apply {u : GL (Fin n) (AfE F E)} (hu : u ∈ UAd hc n) (i j : Fin n) :
    ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j =
      σ ((u : Matrix (Fin n) (Fin n) (AfE F E)) j i - (1 : Matrix (Fin n) (Fin n) (AfE F E)) j i) := by
  rw [PtExist.inv_apply hu, map_sub]
  congr 1
  rcases eq_or_ne i j with rfl | h
  · rw [Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm, map_zero]

include hc in

/- English proof (translation)
Use `valued_sigR hc w (ι (m : E))` as an intermediate fact. Rewrite `this` using `[sigR_inclE, star_natCast, adAt_inclE, adAt_inclE]`. Then use the resulting hypothesis.
-/
theorem valued_nat_conj (w : HeightOneSpectrum (𝓞 E)) (m : ℕ) :
    Valued.v (algebraMap E (w.adicCompletion E) (m : E)) =
      Valued.v (algebraMap E ((conjPrime₂ w).adicCompletion E) (m : E)) := by
  have := valued_sigR hc w (ι (m : E))
  rwa [sigR_inclE, star_natCast, adAt_inclE, adAt_inclE] at this

/- English proof (translation)
Use `set vm : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ) := fun w => Valued.v (algebraMap E (w.adicCompletion E) (m : E)) with hvm`. Establish `hmE : (m : E) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Establish `hm0 : ∀ w, vm w ≠ 0` using `fun w => by`. Simplify using `only [hvm, valued_algebraMap]`. Conclude with `(Valuation.ne_zero_iff _).2 hmE`.

Establish `hmv : ∀ P ∈ Q, P.valuation E (m : E) < 1` using `fun P hP => by`. Use `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P _).2 (hmQ P hP)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hm1 : ∀ P ∈ Q, vm P < 1` using `fun P hP => by`. Simplify using `only [hvm, valued_algebraMap]`.

Conclude with `hmv P hP`. Apply the tactic sequence `choose C hC using fun (P : HeightOneSpectrum (𝓞 E)) (i j : Fin n) => exists_near_entry ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) P (hm0 P)`. Take `⟨CM, hCM⟩ : ∃ CM : HeightOneSpectrum (𝓞 E) → Matrix (Fin n) (Fin n) E, ∀ P i j, Valued.v (adAt F P ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) - algebraMap E _ (CM P i j)) < vm P` from `⟨fun P => Matrix.of (C P), hC⟩`. Establish `hA : ∀ P, ColAd.Sm Valued.v (vm P) (ColAd.locM P z⁻¹ * (CM P).map (algebraMap E _) - 1)`. Introduce `P`.

Establish `hZ : ColAd.locM P z⁻¹ * ColAd.locM P z = 1`. Rewrite using `[← ColAd.locM_mul, inv_mul_cancel, ColAd.locM_one]`. Establish `e : ColAd.locM P z⁻¹ * (CM P).map (algebraMap E _) - 1 = ColAd.locM P z⁻¹ * ((CM P).map (algebraMap E _) - ColAd.locM P z)`. Rewrite using `[Matrix.mul_sub, hZ]`. Rewrite using `[e]`.

Establish `h1 : ColAd.Sm Valued.v 1 (ColAd.locM P z⁻¹)` using `fun i j => hzS P i j`. Establish `h2 : ColAd.Sm Valued.v (vm P) ((CM P).map (algebraMap E _) - ColAd.locM P z)` using `fun i j => by`. Rewrite using `[Matrix.sub_apply, Matrix.map_apply, Valuation.map_sub_swap]`. Conclude with `(hCM P i j).le`. Use `h1.mul h2` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis. Establish `hdet : ∀ P ∈ Q, IsUnit (CM P).det` using `fun P hP => isUnit_iff_ne_zero.2 (det_ne_zero_of_sm (hm1 P hP) hmE (hmv P hP) _ _ (hA P))`. Take `⟨Ci, hCi⟩ : ∃ Ci : HeightOneSpectrum (𝓞 E) → Matrix (Fin n) (Fin n) E, ∀ P ∈ Q, Ci P * CM P = 1` from `⟨fun P => (CM P)⁻¹, fun P hP => Matrix.nonsing_inv_mul _ (hdet P hP)⟩`. Set `G : Matrix (Fin n) (Fin n) (AfE F E)` to `Matrix.of fun i j => PtExist.glue hc Q ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) (fun P => CM P i j) fun P => Ci P j i`. Set `G' : Matrix (Fin n) (Fin n) (AfE F E)` to `Matrix.of fun i j => PtExist.glue hc Q (((z⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) (fun P => Ci P i j) fun P => CM P j i`.

Establish `hG : ∀ w i j, adAt F w (G i j) = _` using `fun w i j => PtExist.adAt_glue hc Q hQ _ _ _ w`. Establish `hG' : ∀ w i j, adAt F w (G' i j) = _` using `fun w i j => PtExist.adAt_glue hc Q hQ _ _ _ w`. Establish `hone : ∀ w i j, adAt F w ((1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ ((1 : Matrix (Fin n) (Fin n) E) i j)` using `fun w i j => by`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `h1 : G' * G = 1`. Use extensionality with `i j`. Use `PtExist.ad_ext fun w => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, map_sum]`. Simplify using `only [map_mul, hG, hG']`.

Use `split_ifs with h h'`. Simplify using `only [← map_mul, ← map_sum]`. Rewrite using `[← Matrix.mul_apply, hCi w h, hone]`. Simplify using `only [← map_mul, ← map_sum, ← star_mul, ← star_sum]`. Rewrite using `[← Matrix.mul_apply, hCi _ h', hone, Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `by_cases e : i = j <;> simp [e, eq_comm]`. Simplify using `only [← map_mul, ← map_sum]`. Rewrite using `[← Matrix.mul_apply, Units.inv_mul]`. Set `g : GL (Fin n) (AfE F E)` to `⟨G, G', mul_eq_one_comm.1 h1, h1⟩`. Establish `hg : g ∈ UAd hc n`.

Rewrite using `[PtExist.mem_uad_iff, ← h1]`. Use `congr 1`. Use extensionality with `i j`. Use `show σ (G j i) = G' i j`. Conclude with `(PtExist.sig_glue hc Q _ _ _).trans (by rw [← PtExist.inv_apply hz]; rfl)`.

Establish `hgQ : g ∈ RatAt Q` using `fun P i j => ⟨CM P.1 i j, (hG P.1 i j).trans (if_pos P.2)⟩`. Establish `hgP : ∀ P ∈ Q, ColAd.locM P g = (CM P).map (algebraMap E _)` using `fun P hP => Matrix.ext fun i j => (hG P i j).trans (if_pos hP)`. Establish `hgw : ∀ w, w ∉ Q → conjPrime₂ w ∉ Q → ColAd.locM w g = ColAd.locM w z` using `fun w h h' => Matrix.ext fun i j => (hG w i j).trans (by rw [if_neg h, if_neg h']; rfl)`. Establish `hu : z⁻¹ * g ∈ UAd hc n` using `mul_mem (inv_mem hz) hg`. Establish `key : ∀ P ∈ Q, ColAd.Sm Valued.v (vm P) (ColAd.locM P (z⁻¹ * g) - 1) ∧ ColAd.Sm Valued.v (vm P) (ColAd.locM P (z⁻¹ * g)⁻¹ - 1)`.

Introduce `P hP`. Establish `e : ColAd.locM P (z⁻¹ * g) = ColAd.locM P z⁻¹ * (CM P).map (algebraMap E _)`. Rewrite using `[ColAd.locM_mul, hgP P hP]`. Use `⟨e ▸ hA P, sm_inv_sub_one (hm1 P hP) (e ▸ hA P) ?_⟩` and prove the remaining obligations. Rewrite using `[← ColAd.locM_mul, mul_inv_cancel, ColAd.locM_one]`.

Establish `all : ∀ w, ColAd.Sm Valued.v (vm w) (ColAd.locM w (z⁻¹ * g) - 1) ∧ ColAd.Sm Valued.v (vm w) (ColAd.locM w (z⁻¹ * g)⁻¹ - 1)`. Introduce `w`. Distinguish the cases in `hw : w ∈ Q`. Conclude with `key w hw`. Distinguish the cases in `hw' : conjPrime₂ w ∈ Q`.

Take `⟨k1, k2⟩` from `key _ hw'`. Establish `ev : vm w = vm (conjPrime₂ w)` using `valued_nat_conj hc w m`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Establish `e` using `inv_sub_one_apply hc (inv_mem hu) i j`. Rewrite `e` using `[inv_inv]`.

Rewrite using `[locM_sub_one_apply, e, valued_sigR, ev, ← locM_sub_one_apply]`. Conclude with `k2 j i`. Establish `e` using `inv_sub_one_apply hc hu i j`. Rewrite using `[locM_sub_one_apply, e, valued_sigR, ev, ← locM_sub_one_apply]`. Conclude with `k1 j i`.

Establish `e1 : ColAd.locM w (z⁻¹ * g) = 1`. Rewrite using `[ColAd.locM_mul, hgw w hw hw', ← ColAd.locM_mul, inv_mul_cancel, ColAd.locM_one]`. Establish `e2 : ColAd.locM w (z⁻¹ * g)⁻¹ = 1`. Use `ColAd.locM_mul (F := F) (P := w) (z⁻¹ * g)⁻¹ (z⁻¹ * g)` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel, ColAd.locM_one, e1, Matrix.mul_one]`.

Conclude with `this.symm`. Rewrite using `[e1, e2, sub_self]`. Conclude with `⟨fun i j => by simp, fun i j => by simp⟩`. Establish `cong : ∀ x : GL (Fin n) (AfE F E), (∀ w, ColAd.Sm Valued.v (vm w) (ColAd.locM w x - 1)) → ColAd.CongOne ((m : ℕ) : 𝓞 E) x`. Introduce `x hx i j`.

Use `(mem_rInt_iff F E _).2 fun w => ?_` and prove the remaining obligations. Rewrite using `[← adAt_apply, map_mul, adAt_inclE, map_natCast, map_inv₀, map_mul, map_inv₀, ← locM_sub_one_apply]`. Conclude with `(inv_mul_le_one₀ (zero_lt_iff.2 (hm0 w))).2 (hx w i j)`. Conclude with `⟨g, hg, hgQ, cong _ fun w => (all w).1, cong _ fun w => (all w).2⟩`.
-/
theorem glue_approx {Q : Finset (HeightOneSpectrum (𝓞 E))} (hQ : ∀ P ∈ Q, conjPrime₂ P ∉ Q) (m : ℕ) (hm : 0 < m)
    (hmQ : ∀ P ∈ Q, ((m : ℕ) : 𝓞 E) ∈ P.asIdeal) {z : GL (Fin n) (AfE F E)} (hz : z ∈ UAd hc n)
    (hzS : ∀ w i j, Valued.v (adAt F w (((z⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1) :
    ∃ g : GL (Fin n) (AfE F E), g ∈ UAd hc n ∧ g ∈ RatAt Q ∧ ColAd.CongOne ((m : ℕ) : 𝓞 E) (z⁻¹ * g) ∧
      ColAd.CongOne ((m : ℕ) : 𝓞 E) (z⁻¹ * g)⁻¹ := by
  classical
  set vm : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ) :=
    fun w => Valued.v (algebraMap E (w.adicCompletion E) (m : E)) with hvm
  have hmE : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hm0 : ∀ w, vm w ≠ 0 := fun w => by
    simp only [hvm, valued_algebraMap]
    exact (Valuation.ne_zero_iff _).2 hmE
  have hmv : ∀ P ∈ Q, P.valuation E (m : E) < 1 := fun P hP => by
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P _).2 (hmQ P hP)
    exact_mod_cast this
  have hm1 : ∀ P ∈ Q, vm P < 1 := fun P hP => by
    simp only [hvm, valued_algebraMap]
    exact hmv P hP
  choose C hC using fun (P : HeightOneSpectrum (𝓞 E)) (i j : Fin n) =>
    exists_near_entry ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) P (hm0 P)
  obtain ⟨CM, hCM⟩ : ∃ CM : HeightOneSpectrum (𝓞 E) → Matrix (Fin n) (Fin n) E, ∀ P i j,
      Valued.v (adAt F P ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) - algebraMap E _ (CM P i j)) < vm P :=
    ⟨fun P => Matrix.of (C P), hC⟩
  have hA : ∀ P, ColAd.Sm Valued.v (vm P) (ColAd.locM P z⁻¹ * (CM P).map (algebraMap E _) - 1) := by
    intro P
    have hZ : ColAd.locM P z⁻¹ * ColAd.locM P z = 1 := by
      rw [← ColAd.locM_mul, inv_mul_cancel, ColAd.locM_one]
    have e : ColAd.locM P z⁻¹ * (CM P).map (algebraMap E _) - 1 =
        ColAd.locM P z⁻¹ * ((CM P).map (algebraMap E _) - ColAd.locM P z) := by
      rw [Matrix.mul_sub, hZ]
    rw [e]
    have h1 : ColAd.Sm Valued.v 1 (ColAd.locM P z⁻¹) := fun i j => hzS P i j
    have h2 : ColAd.Sm Valued.v (vm P) ((CM P).map (algebraMap E _) - ColAd.locM P z) := fun i j => by
      rw [Matrix.sub_apply, Matrix.map_apply, Valuation.map_sub_swap]
      exact (hCM P i j).le
    have := h1.mul h2
    rwa [one_mul] at this
  have hdet : ∀ P ∈ Q, IsUnit (CM P).det := fun P hP =>
    isUnit_iff_ne_zero.2 (det_ne_zero_of_sm (hm1 P hP) hmE (hmv P hP) _ _ (hA P))
  obtain ⟨Ci, hCi⟩ : ∃ Ci : HeightOneSpectrum (𝓞 E) → Matrix (Fin n) (Fin n) E, ∀ P ∈ Q, Ci P * CM P = 1 :=
    ⟨fun P => (CM P)⁻¹, fun P hP => Matrix.nonsing_inv_mul _ (hdet P hP)⟩
  let G : Matrix (Fin n) (Fin n) (AfE F E) := Matrix.of fun i j =>
    PtExist.glue hc Q ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) (fun P => CM P i j) fun P => Ci P j i
  let G' : Matrix (Fin n) (Fin n) (AfE F E) := Matrix.of fun i j =>
    PtExist.glue hc Q (((z⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) (fun P => Ci P i j)
      fun P => CM P j i
  have hG : ∀ w i j, adAt F w (G i j) = _ := fun w i j => PtExist.adAt_glue hc Q hQ _ _ _ w
  have hG' : ∀ w i j, adAt F w (G' i j) = _ := fun w i j => PtExist.adAt_glue hc Q hQ _ _ _ w
  have hone : ∀ w i j, adAt F w ((1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      algebraMap E _ ((1 : Matrix (Fin n) (Fin n) E) i j) := fun w i j => by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h1 : G' * G = 1 := by
    ext i j
    refine PtExist.ad_ext fun w => ?_
    rw [Matrix.mul_apply, map_sum]
    simp only [map_mul, hG, hG']
    split_ifs with h h'
    · simp only [← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, hCi w h, hone]
    · simp only [← map_mul, ← map_sum, ← star_mul, ← star_sum]
      rw [← Matrix.mul_apply, hCi _ h', hone, Matrix.one_apply, Matrix.one_apply]
      by_cases e : i = j <;> simp [e, eq_comm]
    · simp only [← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, Units.inv_mul]
  let g : GL (Fin n) (AfE F E) := ⟨G, G', mul_eq_one_comm.1 h1, h1⟩
  have hg : g ∈ UAd hc n := by
    rw [PtExist.mem_uad_iff, ← h1]
    congr 1
    ext i j
    show σ (G j i) = G' i j
    exact (PtExist.sig_glue hc Q _ _ _).trans (by rw [← PtExist.inv_apply hz]; rfl)
  have hgQ : g ∈ RatAt Q := fun P i j => ⟨CM P.1 i j, (hG P.1 i j).trans (if_pos P.2)⟩
  have hgP : ∀ P ∈ Q, ColAd.locM P g = (CM P).map (algebraMap E _) := fun P hP =>
    Matrix.ext fun i j => (hG P i j).trans (if_pos hP)
  have hgw : ∀ w, w ∉ Q → conjPrime₂ w ∉ Q → ColAd.locM w g = ColAd.locM w z := fun w h h' =>
    Matrix.ext fun i j => (hG w i j).trans (by rw [if_neg h, if_neg h']; rfl)
  have hu : z⁻¹ * g ∈ UAd hc n := mul_mem (inv_mem hz) hg
  have key : ∀ P ∈ Q, ColAd.Sm Valued.v (vm P) (ColAd.locM P (z⁻¹ * g) - 1) ∧
      ColAd.Sm Valued.v (vm P) (ColAd.locM P (z⁻¹ * g)⁻¹ - 1) := by
    intro P hP
    have e : ColAd.locM P (z⁻¹ * g) = ColAd.locM P z⁻¹ * (CM P).map (algebraMap E _) := by
      rw [ColAd.locM_mul, hgP P hP]
    refine ⟨e ▸ hA P, sm_inv_sub_one (hm1 P hP) (e ▸ hA P) ?_⟩
    rw [← ColAd.locM_mul, mul_inv_cancel, ColAd.locM_one]
  have all : ∀ w, ColAd.Sm Valued.v (vm w) (ColAd.locM w (z⁻¹ * g) - 1) ∧
      ColAd.Sm Valued.v (vm w) (ColAd.locM w (z⁻¹ * g)⁻¹ - 1) := by
    intro w
    by_cases hw : w ∈ Q
    · exact key w hw
    by_cases hw' : conjPrime₂ w ∈ Q
    · obtain ⟨k1, k2⟩ := key _ hw'
      have ev : vm w = vm (conjPrime₂ w) := valued_nat_conj hc w m
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have e := inv_sub_one_apply hc (inv_mem hu) i j
        rw [inv_inv] at e
        rw [locM_sub_one_apply, e, valued_sigR, ev, ← locM_sub_one_apply]
        exact k2 j i
      · have e := inv_sub_one_apply hc hu i j
        rw [locM_sub_one_apply, e, valued_sigR, ev, ← locM_sub_one_apply]
        exact k1 j i
    · have e1 : ColAd.locM w (z⁻¹ * g) = 1 := by
        rw [ColAd.locM_mul, hgw w hw hw', ← ColAd.locM_mul, inv_mul_cancel, ColAd.locM_one]
      have e2 : ColAd.locM w (z⁻¹ * g)⁻¹ = 1 := by
        have := ColAd.locM_mul (F := F) (P := w) (z⁻¹ * g)⁻¹ (z⁻¹ * g)
        rw [inv_mul_cancel, ColAd.locM_one, e1, Matrix.mul_one] at this
        exact this.symm
      rw [e1, e2, sub_self]
      exact ⟨fun i j => by simp, fun i j => by simp⟩
  have cong : ∀ x : GL (Fin n) (AfE F E), (∀ w, ColAd.Sm Valued.v (vm w) (ColAd.locM w x - 1)) →
      ColAd.CongOne ((m : ℕ) : 𝓞 E) x := by
    intro x hx i j
    refine (mem_rInt_iff F E _).2 fun w => ?_
    rw [← adAt_apply, map_mul, adAt_inclE, map_natCast, map_inv₀, map_mul, map_inv₀, ← locM_sub_one_apply]
    exact (inv_mul_le_one₀ (zero_lt_iff.2 (hm0 w))).2 (hx w i j)
  exact ⟨g, hg, hgQ, cong _ fun w => (all w).1, cong _ fun w => (all w).2⟩

end Main

open GlobalTheory.SeeSaw.TwLev.GlueApprox in

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc n _ Q hQ m hm hmQ z hz hzS`. Take `⟨y, hy, -⟩` from `St_one_int (inv_mem hzS)`. Use `glue_approx hc hQ m hm hmQ hz fun w i j => ?_` and prove the remaining obligations. Rewrite using `[hy]`. Conclude with `(mem_rInt_iff F E _).1 (y i j).2 w`.
-/
theorem exists_ratAt_congOne : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {n : ℕ} [NeZero n] {Q : Finset (HeightOneSpectrum (𝓞 E))}, (∀ P ∈ Q, conjPrime₂ P ∉ Q) →
    ∀ (m : ℕ), 0 < m → (∀ P ∈ Q, ((m : ℕ) : 𝓞 E) ∈ P.asIdeal) → ∀ (z : GL (Fin n) (AfE F E)), z ∈ UAd hc n →
    z ∈ St (1 : GL (Fin n) (AfE F E)) →
    ∃ g : GL (Fin n) (AfE F E), g ∈ UAd hc n ∧ g ∈ RatAt Q ∧ GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) (z⁻¹ * g) ∧
      GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) (z⁻¹ * g)⁻¹ := by
  intro F E _ _ _ _ _ _ hc n _ Q hQ m hm hmQ z hz hzS
  obtain ⟨y, hy, -⟩ := St_one_int (inv_mem hzS)
  refine glue_approx hc hQ m hm hmQ hz fun w i j => ?_
  rw [hy]
  exact (mem_rInt_iff F E _).1 (y i j).2 w

end GlobalTheory.SeeSaw.TwLev.GlueApprox
