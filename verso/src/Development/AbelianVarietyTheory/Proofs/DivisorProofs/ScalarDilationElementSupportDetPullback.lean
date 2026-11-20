import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DilScalar

variable {D : D7}

/- English proof (translation)
Use `AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy` and prove the remaining obligations. Introduce and unpack `_ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩`. Use `AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_mem (ha w) (hb w)`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Both sides reduce to the same expression. Introduce `x _`. Rewrite using `[zero_mul]`. Conclude with `zero_mem _`.

Introduce `x _`. Rewrite using `[mul_zero]`. Conclude with `zero_mem _`. Introduce `x y z _ _ _ h1 h2`. Rewrite using `[add_mul]`.

Conclude with `add_mem h1 h2`. Introduce `x y z _ _ _ h1 h2`. Rewrite using `[mul_add]`. Conclude with `add_mem h1 h2`. Introduce `x y _ _ h`.

Rewrite using `[neg_mul]`. Conclude with `neg_mem h`. Introduce `x y _ _ h`. Rewrite using `[mul_neg]`. Conclude with `neg_mem h`.
-/
theorem int_mul {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, x, rfl⟩`.
-/
theorem incA_int (x : 𝓞 D.host.E) : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, x, rfl⟩

/- English proof (translation)
Take `⟨a, b, hab⟩` from `P.exists_primeCompl_mul_eq_of_integer _ hv`. Establish `hb : (b : 𝓞 D.host.E) ∉ P.asIdeal` using `b.2`. Establish `hb0 : (b : 𝓞 D.host.E) ≠ 0` using `fun h => hb (h ▸ zero_mem _)`. Establish `hb1 : ((b : 𝓞 D.host.E) : D.host.E) ≠ 0` using `by exact_mod_cast hb0`. Establish `hi : finPart D (e * incA D (((b : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D`.

Assume the negation of the conclusion as `hc`. Conclude with `hb ((he.2 _ hb0).2 hc)`. Establish `hq : y = (a : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E)⁻¹`. Rewrite using `[eq_mul_inv_iff_mul_eq₀ hb1]`. Conclude with `hab`.

Establish `h` using `int_mul (incA_int (D := D) a) hi`. Rewrite `h` using `[← RingHom.map_mul, mul_left_comm, ← map_mul (incA D), ← hq]`. Conclude with `h`.
-/
theorem idemAt_mul_int {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e P)
    {y : D.host.E} (hv : P.valuation D.host.E y ≤ 1) : finPart D (e * incA D y) ∈ intAE D := by
  obtain ⟨a, b, hab⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
  have hb : (b : 𝓞 D.host.E) ∉ P.asIdeal := b.2
  have hb0 : (b : 𝓞 D.host.E) ≠ 0 := fun h => hb (h ▸ zero_mem _)
  have hb1 : ((b : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hb0
  have hi : finPart D (e * incA D (((b : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hc
    exact hb ((he.2 _ hb0).2 hc)
  have hq : y = (a : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hb1]
    exact hab
  have h := int_mul (incA_int (D := D) a) hi
  rw [← RingHom.map_mul, mul_left_comm, ← map_mul (incA D), ← hq] at h
  exact h

/- English proof (translation)
Rewrite using `[P.valuation_of_algebraMap]`. Establish `a1 : P.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ))` using `(P.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)`. Establish `a2 : ¬ P.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ))` using `fun h => h2 ((P.intValuation_le_pow_iff_mem ϖ 2).1 h)`. Establish `a0 : P.intValuation ϖ ≠ 0` using `fun h => a2 (h ▸ zero_le')`. Rewrite `a1`, `a2`, the goal using `[← WithZero.exp_log a0]`.

Rewrite `a1`, `a2` using `[WithZero.exp_le_exp]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_uniformiser (P : HeightOneSpectrum (𝓞 D.host.E)) {ϖ : 𝓞 D.host.E}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) := by
  rw [P.valuation_of_algebraMap]
  have a1 : P.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (P.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ P.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have a0 : P.intValuation ϖ ≠ 0 := fun h => a2 (h ▸ zero_le')
  rw [← WithZero.exp_log a0] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  omega

/- English proof (translation)
Take `⟨⟨es, hes, hsum⟩, -⟩` from `he`. Rewrite using `[hsum, Finset.sum_mul, map_sum]`. Use `sum_mem fun PP hPP => idemAt_mul_int (hes PP hPP) ?_` and prove the remaining obligations. Establish `v1` using `val_uniformiser (D := D) PP (hϖ PP hPP).1 (hϖ PP hPP).2`. Establish `v2 : PP.valuation D.host.E (N : D.host.E) ≤ WithZero.exp (-1 : ℤ)`.

Rewrite using `[← map_natCast (algebraMap (𝓞 D.host.E) D.host.E) N, PP.valuation_of_algebraMap]`. Use `(PP.intValuation_le_pow_iff_mem (N : 𝓞 D.host.E) 1).2 (by rw [pow_one]; exact hN PP hPP)` as an intermediate fact. Simplify using `using this`. Rewrite using `[map_mul, map_inv₀, v1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem idemSum_dil_int {e : AE D} {Q : Finset (Pl D.host.E)} (he : IsIdemSum e Q) {N : ℕ}
    (hN : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) {ϖ : 𝓞 D.host.E}
    (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) :
    finPart D (e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) ∈ intAE D := by
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  rw [hsum, Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => idemAt_mul_int (hes PP hPP) ?_
  have v1 := val_uniformiser (D := D) PP (hϖ PP hPP).1 (hϖ PP hPP).2
  have v2 : PP.valuation D.host.E (N : D.host.E) ≤ WithZero.exp (-1 : ℤ) := by
    rw [← map_natCast (algebraMap (𝓞 D.host.E) D.host.E) N, PP.valuation_of_algebraMap]
    have := (PP.intValuation_le_pow_iff_mem (N : 𝓞 D.host.E) 1).2 (by rw [pow_one]; exact hN PP hPP)
    simpa using this
  rw [map_mul, map_inv₀, v1]
  calc PP.valuation D.host.E (N : D.host.E) * (WithZero.exp (-1 : ℤ))⁻¹
      ≤ WithZero.exp (-1 : ℤ) * (WithZero.exp (-1 : ℤ))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero

end GlobalTheory.DilScalar

set_option maxHeartbeats 1000000 in
open GlobalTheory.DilScalar in

/- English proof (translation)
Introduce `D S T ΛS ΛT Q e he N hN0 hN ϖ hϖ0 hϖ z hz`. Establish `hee : e * e = e` using `idemSum_sq he`. Establish `hec : e * cA D e = 0` using `he.2`. Establish `hcc : cA D e * cA D e = cA D e` using `by rw [← map_mul, hee]`. Establish `hXP : incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) = 1`.

Rewrite using `[← map_mul, inv_mul_cancel₀ hϖ0, map_one]`. Establish `hYZ : cA D (incA D (ϖ : D.host.E)) * cA D (incA D ((ϖ : D.host.E)⁻¹)) = 1`. Rewrite using `[← map_mul, ← map_mul, mul_inv_cancel₀ hϖ0, map_one, map_one]`. Establish `hea : e * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) = e * incA D ((ϖ : D.host.E)⁻¹)`. Take the linear combination `(incA D ((ϖ : D.host.E)⁻¹) - 1) * hee + (cA D (incA D (ϖ : D.host.E)) - 1) * hec`.

Establish `hab : (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) * (e * incA D (ϖ : D.host.E) + cA D e * cA D (incA D ((ϖ : D.host.E)⁻¹)) + (1 - e - cA D e)) = 1`. Take the linear combination `(incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) - incA D ((ϖ : D.host.E)⁻¹) - incA D (ϖ : D.host.E) + 1) * hee + (cA D (incA D (ϖ : D.host.E)) * cA D (incA D ((ϖ : D.host.E)⁻¹)) - cA D (incA D (ϖ : D.host.E)) - cA D (incA D ((ϖ : D.host.E)⁻¹)) + 1) * hcc + (incA D ((ϖ : D.host …`. Establish `hPint : finPart D (incA D (ϖ : D.host.E)) ∈ intAE D` using `incA_int ϖ`. Establish `hPmem : ∀ u ∈ latAll S T ΛS ΛT, incA D (ϖ : D.host.E) • u ∈ latAll S T ΛS ΛT` using `GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hPint`. Establish `hact : ∀ t : WO S T, actO S T z⁻¹ 1 t = t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))`.

Introduce `t`. Establish `h0 : actO S T z⁻¹ 1 t = HMul.hMul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S z)`. Rewrite using `[actO_eq, inv_inv, mt_one']`. Conclude with `congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) => HMul.hMul M (mt S z)) (Matrix.one_mul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)))`. Rewrite using `[h0, hz]`.

Use extensionality with `i j`. Simplify using `only [Matrix.mul_diagonal, Matrix.map_apply]`. Establish `hmapA : ∀ t : WO S T, IsHalf e t → (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) = t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w`. Introduce `t ht`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply]`. Take the linear combination `(incA D ((ϖ : D.host.E)⁻¹) - (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) * ht i j + t i j * hea`. Establish `halfA : ∀ t : WO S T, IsHalf e (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) → IsHalf e t`. Introduce `t h i j`. Establish `h1` using `h i j`.

Simplify using `only [Matrix.map_apply] at h1`. Take the linear combination `(e * incA D (ϖ : D.host.E) + cA D e * cA D (incA D ((ϖ : D.host.E)⁻¹)) + (1 - e - cA D e)) * h1 - (e * t i j - t i j) * hab`. Establish `halfX : ∀ t : WO S T, IsHalf e (t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) → IsHalf e t`. Introduce `t h i j`. Establish `h1` using `h i j`.

Simplify using `only [Matrix.map_apply] at h1`. Take the linear combination `incA D (ϖ : D.host.E) * h1 - (e * t i j - t i j) * hXP`. Establish `hpull : ∀ Ψ : WO S T → ℂ, (∀ t, Ψ t ≠ 0 → IsHalf e t) → actPull (z, (1 : GA D T)) Ψ = fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)`. Introduce `Ψ hΨ`. Use function extensionality and compare the values at `t`.

Use `show Ψ (actO S T z⁻¹ (1 : GA D T)⁻¹ t) = _`. Rewrite using `[inv_one, hact]`. Distinguish the cases in `hh : IsHalf e t`. Rewrite using `[hmapA t hh]`. Establish `h1 : Ψ (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) = 0`.

Assume the negation of the conclusion as `h0`. Conclude with `hh (halfA t (hΨ _ h0))`. Establish `h2 : Ψ (t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) = 0`. Assume the negation of the conclusion as `h0`. Conclude with `hh (halfX t (hΨ _ h0))`.

Rewrite using `[h1, h2]`. Use `⟨?_, ?_, hpull, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Rewrite using `[hz]`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Rewrite using `[Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]`. Take the linear combination `(incA D ((ϖ : D.host.E)⁻¹) - 1) * hee + (cA D (incA D (ϖ : D.host.E)) - 1) * hcc + (incA D ((ϖ : D.host.E)⁻¹) + cA D (incA D (ϖ : D.host.E)) - 2) * hec`. Rewrite using `[Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero, mul_zero]`. Establish `hdet : (mt S z).det * (mt S z⁻¹).det = 1`.

Rewrite using `[← Matrix.det_mul, ← mt_mul', mul_inv_cancel, mt_one', Matrix.det_one]`. Use `⟨⟨cA D e * (mt S z).det + (1 - cA D e), cA D e * (mt S z⁻¹).det + (1 - cA D e), ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Take the linear combination `(cA D e * cA D e) * hdet + (2 - (mt S z).det - (mt S z⁻¹).det) * hcc`. Take the linear combination `(cA D e * cA D e) * hdet + (2 - (mt S z).det - (mt S z⁻¹).det) * hcc`. Introduce `Φ hΦ`.

Establish `hsupp` using `hΦ.1`. Take `⟨_, k, hk, hinv, hcpt⟩` from `hΦ`. Rewrite using `[hpull Φ hsupp]`. Establish `hint` using `idemSum_dil_int he hN hϖ`. Use `⟨fun t ht => halfX t (hsupp _ ht), N * k, Nat.mul_pos (Nat.pos_of_ne_zero hN0) hk, fun u hu hue t => ?_, fun t ht => ?_⟩` and prove the remaining obligations.

Establish `key : (t + (N * k) • u).map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) = t.map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) + k • ((e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) • u)`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_natCast, Nat.cast_mul]`. Take the linear combination `(-((k : AE D) * (N : AE D) * incA D ((ϖ : D.host.E)⁻¹))) * hue i j`. Simplify using `only`.

Rewrite using `[key]`. Use `hinv _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hint u hu) (fun i j => ?_) _` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Take the linear combination `(incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹) * u i j) * hee`. Establish `h1` using `hPmem _ (hcpt _ ht)`.

Establish `h2 : incA D (ϖ : D.host.E) • k • t.map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) = k • t`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul]`. Take the linear combination `((k : AE D) * t i j) * hXP`. Rewrite `h1` using `[h2]`.

Rewrite using `[mul_smul]`. Conclude with `nsmul_mem h1 N`. Introduce `t ht hmem`. Rewrite `hmem` using `[hact, hmapA t ht]`. Establish `h1` using `hPmem _ hmem`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]`. Take the linear combination `(-t i j) * hXP`.
-/
theorem GlobalTheory.DilScalar.scalar_dil_facts : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D S, mt S z = Matrix.diagonal (fun _ => e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) → SuppAt e S z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D e) S z x) ∧ (∀ Ψ : WO S T → ℂ, (∀ t, Ψ t ≠ 0 → IsHalf e t) → actPull (z, (1 : GA D T)) Ψ = fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) ∧ (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsSBHalf e (latAll S T ΛS ΛT) (actPull (z, (1 : GA D T)) Φ)) ∧ ∀ t : WO S T, IsHalf e t → actO S T z⁻¹ 1 t ∈ latAll S T ΛS ΛT → t ∈ latAll S T ΛS ΛT := by
  intro D S T ΛS ΛT Q e he N hN0 hN ϖ hϖ0 hϖ z hz
  have hee : e * e = e := idemSum_sq he
  have hec : e * cA D e = 0 := he.2
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hXP : incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hϖ0, map_one]
  have hYZ : cA D (incA D (ϖ : D.host.E)) * cA D (incA D ((ϖ : D.host.E)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hϖ0, map_one, map_one]
  have hea : e * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) =
      e * incA D ((ϖ : D.host.E)⁻¹) := by
    linear_combination (incA D ((ϖ : D.host.E)⁻¹) - 1) * hee + (cA D (incA D (ϖ : D.host.E)) - 1) * hec
  have hab : (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) *
      (e * incA D (ϖ : D.host.E) + cA D e * cA D (incA D ((ϖ : D.host.E)⁻¹)) + (1 - e - cA D e)) = 1 := by
    linear_combination (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) - incA D ((ϖ : D.host.E)⁻¹)
        - incA D (ϖ : D.host.E) + 1) * hee
      + (cA D (incA D (ϖ : D.host.E)) * cA D (incA D ((ϖ : D.host.E)⁻¹)) - cA D (incA D (ϖ : D.host.E))
        - cA D (incA D ((ϖ : D.host.E)⁻¹)) + 1) * hcc
      + (incA D ((ϖ : D.host.E)⁻¹) * cA D (incA D ((ϖ : D.host.E)⁻¹)) + cA D (incA D (ϖ : D.host.E)) * incA D (ϖ : D.host.E)
        - incA D ((ϖ : D.host.E)⁻¹) - incA D (ϖ : D.host.E) - cA D (incA D (ϖ : D.host.E))
        - cA D (incA D ((ϖ : D.host.E)⁻¹)) + 2) * hec
      + e * hXP + cA D e * hYZ

  have hPint : finPart D (incA D (ϖ : D.host.E)) ∈ intAE D := incA_int ϖ
  have hPmem : ∀ u ∈ latAll S T ΛS ΛT, incA D (ϖ : D.host.E) • u ∈ latAll S T ΛS ΛT :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hPint

  have hact : ∀ t : WO S T, actO S T z⁻¹ 1 t =
      t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) := by
    intro t
    have h0 : actO S T z⁻¹ 1 t = HMul.hMul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S z) := by
      rw [actO_eq, inv_inv, mt_one']; exact congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) => HMul.hMul M (mt S z))
        (Matrix.one_mul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)))
    rw [h0, hz]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.map_apply]
  have hmapA : ∀ t : WO S T, IsHalf e t →
      (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) =
        t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w := by
    intro t ht
    ext i j
    simp only [Matrix.map_apply]
    linear_combination (incA D ((ϖ : D.host.E)⁻¹) -
      (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) * ht i j + t i j * hea
  have halfA : ∀ t : WO S T, IsHalf e (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) +
      cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) → IsHalf e t := by
    intro t h i j
    have h1 := h i j
    simp only [Matrix.map_apply] at h1
    linear_combination (e * incA D (ϖ : D.host.E) + cA D e * cA D (incA D ((ϖ : D.host.E)⁻¹)) + (1 - e - cA D e)) * h1
      - (e * t i j - t i j) * hab
  have halfX : ∀ t : WO S T, IsHalf e (t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) → IsHalf e t := by
    intro t h i j
    have h1 := h i j
    simp only [Matrix.map_apply] at h1
    linear_combination incA D (ϖ : D.host.E) * h1 - (e * t i j - t i j) * hXP
  have hpull : ∀ Ψ : WO S T → ℂ, (∀ t, Ψ t ≠ 0 → IsHalf e t) →
      actPull (z, (1 : GA D T)) Ψ = fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) := by
    intro Ψ hΨ
    funext t
    show Ψ (actO S T z⁻¹ (1 : GA D T)⁻¹ t) = _
    rw [inv_one, hact]
    by_cases hh : IsHalf e t
    · rw [hmapA t hh]
    · have h1 : Ψ (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) +
          (1 - e - cA D e))) = 0 := by
        by_contra h0
        exact hh (halfA t (hΨ _ h0))
      have h2 : Ψ (t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) = 0 := by
        by_contra h0
        exact hh (halfX t (hΨ _ h0))
      rw [h1, h2]
  refine ⟨?_, ?_, hpull, ?_, ?_⟩
  ·
    intro i j
    rw [hz]
    by_cases h : i = j
    · subst h
      rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      linear_combination (incA D ((ϖ : D.host.E)⁻¹) - 1) * hee + (cA D (incA D (ϖ : D.host.E)) - 1) * hcc +
        (incA D ((ϖ : D.host.E)⁻¹) + cA D (incA D (ϖ : D.host.E)) - 2) * hec
    · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero, mul_zero]
  ·
    have hdet : (mt S z).det * (mt S z⁻¹).det = 1 := by
      rw [← Matrix.det_mul, ← mt_mul', mul_inv_cancel, mt_one', Matrix.det_one]
    refine ⟨⟨cA D e * (mt S z).det + (1 - cA D e), cA D e * (mt S z⁻¹).det + (1 - cA D e), ?_, ?_⟩, rfl⟩
    · linear_combination (cA D e * cA D e) * hdet + (2 - (mt S z).det - (mt S z⁻¹).det) * hcc
    · linear_combination (cA D e * cA D e) * hdet + (2 - (mt S z).det - (mt S z⁻¹).det) * hcc
  ·
    intro Φ hΦ
    have hsupp := hΦ.1
    obtain ⟨_, k, hk, hinv, hcpt⟩ := hΦ
    rw [hpull Φ hsupp]
    have hint := idemSum_dil_int he hN hϖ
    refine ⟨fun t ht => halfX t (hsupp _ ht), N * k, Nat.mul_pos (Nat.pos_of_ne_zero hN0) hk,
      fun u hu hue t => ?_, fun t ht => ?_⟩
    · have key : (t + (N * k) • u).map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) =
          t.map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) +
            k • ((e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) • u) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul, map_mul,
          map_natCast, Nat.cast_mul]
        linear_combination (-((k : AE D) * (N : AE D) * incA D ((ϖ : D.host.E)⁻¹))) * hue i j
      dsimp only
      rw [key]
      refine hinv _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hint u hu) (fun i j => ?_) _
      simp only [Matrix.smul_apply, smul_eq_mul]
      linear_combination (incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹) * u i j) * hee
    · have h1 := hPmem _ (hcpt _ ht)
      have h2 : incA D (ϖ : D.host.E) • k • t.map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) = k • t := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul]
        linear_combination ((k : AE D) * t i j) * hXP
      rw [h2] at h1
      rw [mul_smul]
      exact nsmul_mem h1 N
  ·
    intro t ht hmem
    rw [hact, hmapA t ht] at hmem
    have h1 := hPmem _ hmem
    convert h1 using 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (-t i j) * hXP
