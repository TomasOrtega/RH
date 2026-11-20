import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MacdonaldHecke
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.CompletionAtPlace.Inertia

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

noncomputable section

namespace GlobalTheory.WhittakerRecursion

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
open scoped ValuativeRel

/- English proof (translation)
Set `e : {x // x ∈ S} ≃ {x // x ∈ T}` to `Finset.equivOfCardEq h`. Use `⟨e.extendSubtype, funext fun i => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hi : i ∈ S`. Use `Equiv.extendSubtype_mem e i hi` as an intermediate fact. Simplify using `[Spherical.lamS, hi, this]`.

Use `Equiv.extendSubtype_not_mem e i hi` as an intermediate fact. Simplify using `[Spherical.lamS, hi, this]`.
-/
theorem lamS_perm {n : ℕ} (S T : Finset (Fin n)) (h : S.card = T.card) :
    ∃ σ : Equiv.Perm (Fin n), Spherical.lamS T ∘ σ = Spherical.lamS S := by
  classical
  let e : {x // x ∈ S} ≃ {x // x ∈ T} := Finset.equivOfCardEq h
  refine ⟨e.extendSubtype, funext fun i => ?_⟩
  by_cases hi : i ∈ S
  · have := Equiv.extendSubtype_mem e i hi
    simp [Spherical.lamS, hi, this]
  · have := Equiv.extendSubtype_not_mem e i hi
    simp [Spherical.lamS, hi, this]

/- English proof (translation)
Set `T : Finset (Fin n)` to `Finset.univ.filter fun i => i.val < r`. Establish `hT : T.card = r`. Simplify using `[T, Fin.card_filter_val_lt, hr]`. Establish `hD : ((Iwasawa.torusPow F n (Spherical.lamS T) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r`. Rewrite using `[Iwasawa.coe_torusPow, Formalism.UG.diagJ]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases hi : i.val < r <;> simp [Spherical.lamS, T, hi]`. Establish `hU : ∀ (S : Finset (Fin n)) c, Spherical.unipC (F` using `F) S c ∈ GLnLocal.integralGL F n := by`. Introduce `S c`.

Use `(Spherical.torusPow_conj_unipC_mem (l := 0) antitone_const S c).2` as an intermediate fact. Establish `h0 : Iwasawa.torusPow F n 0 = 1` using `Units.ext (by simp [Iwasawa.coe_torusPow])`. Simplify `this` using `[h0]`. Rewrite using `[← hD]`. Prove the components needed by the constructor for the conclusion.

Introduce `hg`. Take `⟨S, hS, c, hc⟩` from `Spherical.exists_gMat hg`. Establish `hk` using `QuotientGroup.eq.1 hc`. Take `⟨σ, hσ⟩` from `lamS_perm S T (hS.trans hT.symm)`. Establish `hp` using `GLnLocal.permGL_mem_integralGL F n σ`.

Use `⟨_, mul_mem (hU S c) (inv_mem hp), _, mul_mem hp hk, ?_⟩` and prove the remaining obligations. Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Establish `h1` using `Spherical.permGL_conj_torusPow (F := F) σ (Spherical.lamS T)`. Rewrite `h1` using `[hσ]`.

Rewrite using `[Spherical.gMat, ← h1]`. Use `group`. Introduce and unpack `⟨a, ha, b, hb, e⟩`. Rewrite `e` using `[← Units.val_mul, ← Units.val_mul]`. Establish `e'` using `Units.ext e`.

Establish `h0` using `Spherical.gMat_mem_minusculeSet (F := F) T (fun _ => 0)`. Rewrite `h0` using `[hT]`. Use `Spherical.mul_mem_minusculeSet h0 (mul_mem ha (inv_mem (hU T fun _ => 0))) hb` as an intermediate fact. Rewrite using `[e']`. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[Spherical.gMat]`. Use `group`.
-/
theorem mem_minusculeSet_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) F) :
    g ∈ Spherical.minusculeSet F n r ↔ ∃ a ∈ GLnLocal.integralGL F n, ∃ b ∈ GLnLocal.integralGL F n,
      (g : Matrix (Fin n) (Fin n) F) = (a : Matrix (Fin n) (Fin n) F) *
        Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r * (b : Matrix (Fin n) (Fin n) F) := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter fun i => i.val < r
  have hT : T.card = r := by
    simp [T, Fin.card_filter_val_lt, hr]
  have hD : ((Iwasawa.torusPow F n (Spherical.lamS T) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r := by
    rw [Iwasawa.coe_torusPow, Formalism.UG.diagJ]
    congr 1
    funext i
    by_cases hi : i.val < r <;> simp [Spherical.lamS, T, hi]
  have hU : ∀ (S : Finset (Fin n)) c, Spherical.unipC (F := F) S c ∈ GLnLocal.integralGL F n := by
    intro S c
    have := (Spherical.torusPow_conj_unipC_mem (l := 0) antitone_const S c).2
    have h0 : Iwasawa.torusPow F n 0 = 1 := Units.ext (by simp [Iwasawa.coe_torusPow])
    simpa [h0] using this
  rw [← hD]
  constructor
  · intro hg
    obtain ⟨S, hS, c, hc⟩ := Spherical.exists_gMat hg
    have hk := QuotientGroup.eq.1 hc
    obtain ⟨σ, hσ⟩ := lamS_perm S T (hS.trans hT.symm)
    have hp := GLnLocal.permGL_mem_integralGL F n σ
    refine ⟨_, mul_mem (hU S c) (inv_mem hp), _, mul_mem hp hk, ?_⟩
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    have h1 := Spherical.permGL_conj_torusPow (F := F) σ (Spherical.lamS T)
    rw [hσ] at h1
    rw [Spherical.gMat, ← h1]
    group
  · rintro ⟨a, ha, b, hb, e⟩
    rw [← Units.val_mul, ← Units.val_mul] at e
    have e' := Units.ext e
    have h0 := Spherical.gMat_mem_minusculeSet (F := F) T (fun _ => 0)
    rw [hT] at h0
    have := Spherical.mul_mem_minusculeSet h0 (mul_mem ha (inv_mem (hU T fun _ => 0))) hb
    rw [e']
    convert this using 1
    rw [Spherical.gMat]
    group

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

/- English proof (translation)
Use `letI : Fintype 𝓀[F] := Fintype.ofFinite _`. Use `letI : MeasurableSpace (GL (Fin n) F) := borel _`. Use `haveI : BorelSpace (GL (Fin n) F) := ⟨rfl⟩`. Use `set Cs : Finset (GL (Fin n) F ⧸ integralGL F n) := (Finset.univ.powersetCard r).biUnion fun S => Finset.univ.image fun c : Pairs S → 𝓀[F] => (QuotientGroup.mk (gMat S c) : _)`. Rewrite using `[finsum_eq_sum_of_support_subset (s := Cs)]`.

Rewrite using `[Finset.sum_biUnion]`. Use `Finset.sum_congr rfl fun S hS => ?_` and prove the remaining obligations. Establish `hSr` using `(Finset.mem_powersetCard.1 hS).2`. Rewrite using `[Finset.sum_image fun c _ c' _ h => gMat_injective S h]`. Use `Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (sum_gMat_torusPow hN hl S)` and prove the remaining obligations.

Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (integralGL F n) (gMat S c)`. Establish `hm` using `mul_mem_minusculeSet (hSr ▸ gMat_mem_minusculeSet (F := F) S c) (one_mem _) k.2`. Rewrite `hm` using `[one_mul]`. Rewrite using `[hk, Set.indicator_of_mem hm, one_smul, ← mul_assoc, hf _ k k.2]`. Introduce `S _ S' _ hne`.

Simplify using `only [Function.onFun]`. Rewrite using `[Finset.disjoint_left]`. Introduce `x hx hx'`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨c', -, hc'⟩` from `Finset.mem_image.1 hx'`.

Use `congrArg (fun x : GL (Fin n) F ⧸ integralGL F n => iwasawaExponent F n x.out) hc'` as an intermediate fact. Simplify using `only [iwasawaExponent_out, iwasawaExponent_gMat] at this`. Conclude with `hne (lamS_injective this).symm`. Introduce `x hx`. Establish `hm : x.out ∈ minusculeSet F n r`.

Assume the negation of the conclusion as `hm`. Apply `hx` to reduce the goal to its premises. Simplify using `only [Set.indicator_of_notMem hm, zero_smul]`. Take `⟨S, hS, c, hc⟩` from `exists_gMat hm`. Rewrite `hc` using `[QuotientGroup.out_eq']`.

Conclude with `Finset.mem_biUnion.2 ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS⟩, Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc⟩⟩`.
-/
theorem finsum_minuscule {f : GL (Fin n) F → ℂ} (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hN : ∀ u ∈ unipotent F n ⊓ integralGL F n, ∀ g, f (u * g) = f g) {l : Fin n → ℤ} (hl : Antitone l) (r : ℕ) :
    ∑ᶠ x : GL (Fin n) F ⧸ integralGL F n,
        (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) x.out • f (torusPow F n l * x.out) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, (kappa F S : ℂ) * f (torusPow F n (l + lamS S)) := by
  letI : Fintype 𝓀[F] := Fintype.ofFinite _
  letI : MeasurableSpace (GL (Fin n) F) := borel _
  haveI : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  set Cs : Finset (GL (Fin n) F ⧸ integralGL F n) := (Finset.univ.powersetCard r).biUnion
    fun S => Finset.univ.image fun c : Pairs S → 𝓀[F] => (QuotientGroup.mk (gMat S c) : _)
  rw [finsum_eq_sum_of_support_subset (s := Cs)]
  · rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun S hS => ?_
      have hSr := (Finset.mem_powersetCard.1 hS).2
      rw [Finset.sum_image fun c _ c' _ h => gMat_injective S h]
      refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (sum_gMat_torusPow hN hl S)
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) (gMat S c)
      have hm := mul_mem_minusculeSet (hSr ▸ gMat_mem_minusculeSet (F := F) S c) (one_mem _) k.2
      rw [one_mul] at hm
      rw [hk, Set.indicator_of_mem hm, one_smul, ← mul_assoc, hf _ k k.2]
    · intro S _ S' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨c', -, hc'⟩ := Finset.mem_image.1 hx'
      have := congrArg (fun x : GL (Fin n) F ⧸ integralGL F n => iwasawaExponent F n x.out) hc'
      simp only [iwasawaExponent_out, iwasawaExponent_gMat] at this
      exact hne (lamS_injective this).symm
  · intro x hx
    have hm : x.out ∈ minusculeSet F n r := by
      by_contra hm
      apply hx
      simp only [Set.indicator_of_notMem hm, zero_smul]
    obtain ⟨S, hS, c, hc⟩ := exists_gMat hm
    rw [QuotientGroup.out_eq'] at hc
    exact Finset.mem_biUnion.2 ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS⟩,
      Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc⟩⟩

/- English proof (translation)
Rewrite using `[div_eq_inv_mul, Complex.cpow_mul_int]`. Use `congr 1`. Rewrite using `[sqrtQ, Real.coe_sqrt, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]`. Simplify using the standard rewrite rules.
-/
theorem sqrtQ_zpow (m : ℤ) : sqrtQ F ^ m = (qF F : ℂ) ^ ((m : ℂ) / 2) := by
  rw [div_eq_inv_mul, Complex.cpow_mul_int]
  congr 1
  rw [sqrtQ, Real.coe_sqrt, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
  simp

/- English proof (translation)
Rewrite using `[sqrtQ_zpow, rhoPair]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem cpow_eq_sqrtQ (m : Fin n → ℕ) :
    (qF F : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * ((m k : ℕ) : ℂ))) / 2) =
      sqrtQ F ^ rhoPair (fun i => (m i : ℤ)) := by
  rw [sqrtQ_zpow, rhoPair]
  push_cast
  rfl

end Local

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}

variable (w n) in

/- English proof (translation)
Establish `hO : Ov E w = (ValuativeRel.valuation (w.adicCompletion E)).integer` using `Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm`. Rewrite using `[hO]`. Both sides reduce to the same expression.
-/
theorem integralGL_eq : integralGL (w.adicCompletion E) n = GLint (Fin n) (Ov E w) := by
  have hO : Ov E w = (ValuativeRel.valuation (w.adicCompletion E)).integer :=
    Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm
  rw [hO]
  rfl

variable (w) in

/- English proof (translation)
The claim follows from `GroundTheory.Global.valued_of_irreducible_integer w (GLnLocal.irreducible_uniformizer _)`.
-/
theorem isUnifV_uniformizer : IsUnifV E w (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) :=
  GroundTheory.Global.valued_of_irreducible_integer w (GLnLocal.irreducible_uniformizer _)

variable (w) in

/- English proof (translation)
Unfold `Tj`. Rewrite using `[← integralGL_eq]`. Use `congr 1`. Use extensionality with `g`. Conclude with `(mem_minusculeSet_iff hr g).symm`.
-/
theorem Tj_eq_indicator {r : ℕ} (hr : r ≤ n) :
    Tj ℂ n (Ov E w) (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) r =
      (minusculeSet (w.adicCompletion E) n r).indicator fun _ => (1 : ℂ) := by
  unfold Tj
  rw [← integralGL_eq]
  congr 1
  ext g
  exact (mem_minusculeSet_iff hr g).symm

/- English proof (translation)
Establish `hπ` using `isUnifV_uniformizer w`. Use `set d : Fin n → (w.adicCompletion E)ˣ := fun i => ((uniformizerUnit (w.adicCompletion E))⁻¹ * ϖ) ^ m i`. Establish `hv : ∀ i, Valued.v (d i : w.adicCompletion E) = 1` using `fun i => by`. Simplify using `only [d, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val, coe_uniformizerUnit, map_pow, map_mul, map_inv₀]`. Rewrite using `[hπ, hϖ, inv_mul_cancel₀ WithZero.coe_ne_zero, one_pow]`.

Establish `hd : diagGL (w.adicCompletion E) n d ∈ integralGL (w.adicCompletion E) n`. Rewrite using `[mem_integralGL_iff, ← map_inv]`. Apply the tactic sequence `constructor <;> intro i j <;> rw [coe_diagGL, Matrix.diagonal_apply] <;> split_ifs`. Conclude with `(GroundTheory.Global.mem_valuationInteger_iff w _).2 (hv i).le`. Conclude with `zero_mem _`.

Use `(GroundTheory.Global.mem_valuationInteger_iff w _).2 ?_` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]`. Conclude with `zero_mem _`. Rewrite using `[← hK (torusPow _ _ _) _ hd, torusPow, ← map_mul]`. Use `congr 1`.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[coe_diagGL]`. Express the relevant statement in the definitionally equal form `Matrix.diagonal _ = _`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `[d, mul_pow]`.
-/
theorem apply_diag_eq {W : GL (Fin n) (w.adicCompletion E) → ℂ}
    (hK : ∀ g, ∀ k ∈ integralGL (w.adicCompletion E) n, W (g * k) = W g)
    {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (m : Fin n → ℕ) :
    W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
      (MulEquiv.piUnits.symm fun i => ϖ ^ m i)) = W (torusPow (w.adicCompletion E) n fun i => (m i : ℤ)) := by
  have hπ := isUnifV_uniformizer w
  set d : Fin n → (w.adicCompletion E)ˣ := fun i => ((uniformizerUnit (w.adicCompletion E))⁻¹ * ϖ) ^ m i
  have hv : ∀ i, Valued.v (d i : w.adicCompletion E) = 1 := fun i => by
    simp only [d, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val, coe_uniformizerUnit, map_pow,
      map_mul, map_inv₀]
    rw [hπ, hϖ, inv_mul_cancel₀ WithZero.coe_ne_zero, one_pow]
  have hd : diagGL (w.adicCompletion E) n d ∈ integralGL (w.adicCompletion E) n := by
    rw [mem_integralGL_iff, ← map_inv]
    constructor <;> intro i j <;> rw [coe_diagGL, Matrix.diagonal_apply] <;> split_ifs
    · exact (GroundTheory.Global.mem_valuationInteger_iff w _).2 (hv i).le
    · exact zero_mem _
    · refine (GroundTheory.Global.mem_valuationInteger_iff w _).2 ?_
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
    · exact zero_mem _
  rw [← hK (torusPow _ _ _) _ hd, torusPow, ← map_mul]
  congr 1
  refine Units.ext ?_
  rw [coe_diagGL]
  change Matrix.diagonal _ = _
  congr 1
  funext i
  simp [d, mul_pow]

/- English proof (translation)
Introduce `E _ _ w n ψ hψ W α hN hK hT ϖ hϖ l hl j hj`. Establish `hKK : integralGL (w.adicCompletion E) n = KGL w n` using `integralGL_eq w n`. Establish `hπ` using `isUnifV_uniformizer w`. Establish `hq : qF (w.adicCompletion E) = qV E w`. Unfold `qF qV`.

Rewrite using `[GroundTheory.Global.natCard_residueField_integer, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hsq : sqrtQ (w.adicCompletion E) ^ (j * (n - j)) = (qV E w : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2)`. Rewrite using `[← zpow_natCast, sqrtQ_zpow, hq]`. Move the coercions through the operations in `[Nat.cast_sub hj]`. Both sides reduce to the same expression.

Establish `hK' : ∀ g, ∀ k ∈ integralGL (w.adicCompletion E) n, W (g * k) = W g` using `hKK ▸ hK`. Establish `hN' : ∀ u ∈ unipotent (w.adicCompletion E) n ⊓ integralGL (w.adicCompletion E) n, ∀ g, W (u * g) = W g`. Introduce `u hu g`. Take `⟨hu, hi⟩` from `(mem_unipotent_inf_integralGL_iff _ n).1 hu`. Rewrite using `[hN u ((GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => hu.1 hij, hu.2⟩)]`.

Establish `h1 : GlobalTheory.Whittaker.superDiag u ∈ Ov E w`. Unfold `GlobalTheory.Whittaker.superDiag`. Use `sum_mem fun i _ => sum_mem fun j _ => ?_` and prove the remaining obligations. Conclude with `(GroundTheory.Global.mem_valuationInteger_iff w _).1 (hi i j)`. Establish `h2` using `(hψ 1).2 (one_mem _) _ h1`.

Rewrite `h2` using `[one_mul]`. Rewrite using `[h2, one_mul]`. Establish `hl' : Antitone fun i => (l i : ℤ)` using `fun a b h => Int.ofNat_le.2 (hl h)`. Establish `h` using `congrFun (hT _ hπ j hj) (torusPow (w.adicCompletion E) n fun i => (l i : ℤ))`. Rewrite `h` using `[heckeVec_rightReg (Final.GLintComm E w n) (Tj_mem_hecke hπ j), Tj_eq_indicator w hj, hAct, ← integralGL_eq w n, finsum_minuscule hK' hN' hl', satEig, ← hsq, Multiset.map_map, Pi.smul_apply, smul_eq_mul]`.

Establish `h0 : sqrtQ (w.adicCompletion E) ≠ 0` using `sqrtQ_ne_zero`. Use `mul_left_cancel₀ (pow_ne_zero (j * (n - j)) h0) ?_` and prove the remaining obligations. Rewrite using `[apply_diag_eq hK' hϖ, ← hq, cpow_eq_sqrtQ, Finset.mul_sum]`. Establish `e : (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j) = Finset.univ.powersetCard j`. Use extensionality with `J`.

Simplify using `[Finset.mem_powersetCard]`. Rewrite using `[e]`. Use `Eq.trans ?_ ((congrArg (sqrtQ (w.adicCompletion E) ^ rhoPair (fun i => (l i : ℤ)) * ·) h).trans (by` and prove the remaining obligations. Simplify using `only [Function.comp_def]`. Use the proof step `ring))`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun S hS => ?_` and prove the remaining obligations. Establish `hc : (fun i => (((l + (fun i => if i ∈ S then 1 else 0) : Fin n → ℕ) i : ℕ) : ℤ)) = (fun i => (l i : ℤ)) + lamS S`. Use function extensionality and compare the values at `i`. Simplify using `[lamS]`.

Establish `hr : rhoPair ((fun i => (l i : ℤ)) + lamS S) = rhoPair (fun i => (l i : ℤ)) + rhoPair (lamS S)`. Simplify using `[rhoPair, mul_add, Finset.sum_add_distrib]`. Rewrite using `[apply_diag_eq hK' hϖ, cpow_eq_sqrtQ, hc, ← kappa_mul_halfModulus hj (Finset.mem_powersetCard.1 hS).2, halfModulus_eq, hr, zpow_add₀ h0, zpow_neg]`. Use `zpow_ne_zero (rhoPair (lamS S)) h0` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem recursion : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w n, W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w n) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), ((qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ) k : ℕ) : ℂ))) / 2) * W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ) i))) = (Finset.univ.val.map fun i => (α i : ℂ)).esymm j * ((qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l) k : ℕ) : ℂ))) / 2) * W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i))) := by
  intro E _ _ w n ψ hψ W α hN hK hT ϖ hϖ l hl j hj
  have hKK : integralGL (w.adicCompletion E) n = KGL w n := integralGL_eq w n
  have hπ := isUnifV_uniformizer w
  have hq : qF (w.adicCompletion E) = qV E w := by
    unfold qF qV
    rw [GroundTheory.Global.natCard_residueField_integer, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : sqrtQ (w.adicCompletion E) ^ (j * (n - j)) = (qV E w : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) := by
    rw [← zpow_natCast, sqrtQ_zpow, hq]
    push_cast [Nat.cast_sub hj]
    rfl
  have hK' : ∀ g, ∀ k ∈ integralGL (w.adicCompletion E) n, W (g * k) = W g := hKK ▸ hK
  have hN' : ∀ u ∈ unipotent (w.adicCompletion E) n ⊓ integralGL (w.adicCompletion E) n, ∀ g, W (u * g) = W g := by
    intro u hu g
    obtain ⟨hu, hi⟩ := (mem_unipotent_inf_integralGL_iff _ n).1 hu
    rw [hN u ((GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => hu.1 hij, hu.2⟩)]
    have h1 : GlobalTheory.Whittaker.superDiag u ∈ Ov E w := by
      unfold GlobalTheory.Whittaker.superDiag
      refine sum_mem fun i _ => sum_mem fun j _ => ?_
      exact (GroundTheory.Global.mem_valuationInteger_iff w _).1 (hi i j)
    have h2 := (hψ 1).2 (one_mem _) _ h1
    rw [one_mul] at h2
    rw [h2, one_mul]
  have hl' : Antitone fun i => (l i : ℤ) := fun a b h => Int.ofNat_le.2 (hl h)
  have h := congrFun (hT _ hπ j hj) (torusPow (w.adicCompletion E) n fun i => (l i : ℤ))
  rw [heckeVec_rightReg (Final.GLintComm E w n) (Tj_mem_hecke hπ j),
    Tj_eq_indicator w hj, hAct, ← integralGL_eq w n, finsum_minuscule hK' hN' hl', satEig, ← hsq,
    Multiset.map_map, Pi.smul_apply, smul_eq_mul] at h
  have h0 : sqrtQ (w.adicCompletion E) ≠ 0 := sqrtQ_ne_zero
  refine mul_left_cancel₀ (pow_ne_zero (j * (n - j)) h0) ?_
  rw [apply_diag_eq hK' hϖ, ← hq, cpow_eq_sqrtQ, Finset.mul_sum]
  have e : (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j) = Finset.univ.powersetCard j := by
    ext J; simp [Finset.mem_powersetCard]
  rw [e]
  refine Eq.trans ?_ ((congrArg (sqrtQ (w.adicCompletion E) ^ rhoPair (fun i => (l i : ℤ)) * ·) h).trans (by
    simp only [Function.comp_def]; ring))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hc : (fun i => (((l + (fun i => if i ∈ S then 1 else 0) : Fin n → ℕ) i : ℕ) : ℤ)) =
      (fun i => (l i : ℤ)) + lamS S := by
    funext i
    simp [lamS]
  have hr : rhoPair ((fun i => (l i : ℤ)) + lamS S) = rhoPair (fun i => (l i : ℤ)) + rhoPair (lamS S) := by
    simp [rhoPair, mul_add, Finset.sum_add_distrib]
  rw [apply_diag_eq hK' hϖ, cpow_eq_sqrtQ, hc, ← kappa_mul_halfModulus hj (Finset.mem_powersetCard.1 hS).2,
    halfModulus_eq, hr, zpow_add₀ h0, zpow_neg]
  have := zpow_ne_zero (rhoPair (lamS S)) h0
  field_simp

end GlobalTheory.WhittakerRecursion
