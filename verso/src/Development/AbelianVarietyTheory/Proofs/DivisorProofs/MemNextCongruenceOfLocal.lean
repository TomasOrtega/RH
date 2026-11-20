import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomVal

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published

namespace GlobalTheory.TamCnt.LevelUp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

/- English proof (translation)
Conclude with `RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v a`.
-/
theorem ev_same (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : evalV F v (singleV F v a) = a := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v a

/- English proof (translation)
Conclude with `RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) a h`.
-/
theorem ev_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (a : Fv F v) : evalV F w (singleV F v a) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) a h

/- English proof (translation)
The claim follows from `RestrictedProduct.ext _ _ fun w => h w`.
-/
theorem af_ext {a b : Af F} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  RestrictedProduct.ext _ _ fun w => h w

def singleL (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] Af F where
  toFun := singleV F v
  map_add' x y := af_ext fun w => by
    by_cases hw : w = v
    · subst hw; rw [map_add, ev_same, ev_same, ev_same]
    · rw [map_add, ev_ne hw, ev_ne hw, ev_ne hw, add_zero]
  map_smul' c x := af_ext fun w => by
    by_cases hw : w = v
    · subst hw; rw [map_smul, ev_same, ev_same]; rfl
    · rw [map_smul, ev_ne hw, ev_ne hw, smul_zero]

/- English proof (translation)
The claim follows from `af_ext fun w => by by_cases hw : w = v · subst hw; rw [map_mul, ev_same, ev_same, one_mul] · rw [map_mul, ev_ne hw, ev_ne hw, zero_mul]`.
-/
theorem single_ev (v : HeightOneSpectrum (𝓞 F)) (b : Af F) :
    singleV F v (evalV F v b) = singleV F v 1 * b := af_ext fun w => by
  by_cases hw : w = v
  · subst hw; rw [map_mul, ev_same, ev_same, one_mul]
  · rw [map_mul, ev_ne hw, ev_ne hw, zero_mul]

/- English proof (translation)
Introduce `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[ev_same]`. Conclude with `ha`.

Rewrite using `[ev_ne hw]`. Conclude with `zero_mem _`.
-/
theorem single_int {v : HeightOneSpectrum (𝓞 F)} {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) :
    singleV F v a ∈ intAf F := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [ev_same]; exact ha
  · rw [ev_ne hw]; exact zero_mem _

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul, one_mul, ← single_ev]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => rw [mul_add, map_add, map_add, hx, hy]`.
-/
theorem idem_mul (v : HeightOneSpectrum (𝓞 F)) (y : Af F ⊗[F] E) :
    (singleV F v 1 ⊗ₜ[F] (1 : E)) * y =
      TensorProduct.map (singleL v) LinearMap.id (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul, one_mul,
      ← single_ev]
    rfl
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Conclude with `AddSubgroup.subset_closure ⟨evalV F v a, ha v, x, hx, rfl⟩`. Consider the case `zero => simp only [Pi.zero_apply, map_zero, mul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => simp only [Pi.add_apply, map_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => simp only [Pi.neg_apply, map_neg]`. Conclude with `neg_mem hx`.
-/
theorem ev_mem_compLat (v : HeightOneSpectrum (𝓞 F)) (L : Set (Fin M → E)) {y : Fin M → Af F ⊗[F] E}
    (hy : y ∈ latHat F E L) :
    (fun i => Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (y i)) ∈ compLat v L := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨evalV F v a, ha v, x, hx, rfl⟩
  | zero => simp only [Pi.zero_apply, map_zero, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, map_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Conclude with `AddSubgroup.subset_closure ⟨singleV F v a, single_int ha, x, hx, rfl⟩`. Consider the case `zero => simp only [Pi.zero_apply, map_zero, mul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => simp only [Pi.add_apply, map_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => simp only [Pi.neg_apply, map_neg]`. Conclude with `neg_mem hx`.
-/
theorem single_mem_latHat (v : HeightOneSpectrum (𝓞 F)) (L : Set (Fin M → E)) {y : Fin M → Fv F v ⊗[F] E}
    (hy : y ∈ compLat v L) :
    (fun i => TensorProduct.map (singleL v) LinearMap.id (y i)) ∈ latHat F E L := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨singleV F v a, single_int ha, x, hx, rfl⟩
  | zero => simp only [Pi.zero_apply, map_zero, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, map_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx

/- English proof (translation)
Establish `hne : ¬ v.asIdeal ≤ w.asIdeal` using `fun hle => h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)`. Take `⟨p, hp, hpw⟩` from `SetLike.not_le_iff_exists.1 hne`. Establish `h0 : (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot`. Establish `h1` using `(FractionalIdeal.mem_inv_iff h0).1 ht (algebraMap (𝓞 F) F p) (FractionalIdeal.mem_coeIdeal_of_mem _ hp)`. Take `⟨d, hd⟩` from `(FractionalIdeal.mem_one_iff _).1 h1`.

Establish `hv : w.valuation F (algebraMap (𝓞 F) F p) = 1`. Use `le_antisymm (w.valuation_le_one p) (not_lt.1 fun hlt => hpw ?_)` and prove the remaining obligations. Conclude with `(w.valuation_lt_one_iff_mem p).1 hlt`. Establish `h2 : w.valuation F t ≤ 1`. Use `w.valuation_le_one (K := F) d` as an intermediate fact.

Express the relevant statement in the definitionally equal form `w.valuation F (algebraMap (𝓞 F) F d) ≤ 1 at this`. Rewrite `this` using `[hd, map_mul, hv, mul_one]`. Then use the resulting hypothesis. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Express the relevant statement in the definitionally equal form `Valued.v (t : w.adicCompletion F) ≤ 1`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation']` and apply the resulting hypothesis.
-/
theorem inv_int_away {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) {t : F}
    (ht : t ∈ ((v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹)) :
    algebraMap F (Fv F w) t ∈ w.adicCompletionIntegers F := by
  have hne : ¬ v.asIdeal ≤ w.asIdeal := fun hle =>
    h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)
  obtain ⟨p, hp, hpw⟩ := SetLike.not_le_iff_exists.1 hne
  have h0 : (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot
  have h1 := (FractionalIdeal.mem_inv_iff h0).1 ht (algebraMap (𝓞 F) F p)
    (FractionalIdeal.mem_coeIdeal_of_mem _ hp)
  obtain ⟨d, hd⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  have hv : w.valuation F (algebraMap (𝓞 F) F p) = 1 := by
    refine le_antisymm (w.valuation_le_one p) (not_lt.1 fun hlt => hpw ?_)
    exact (w.valuation_lt_one_iff_mem p).1 hlt
  have h2 : w.valuation F t ≤ 1 := by
    have := w.valuation_le_one (K := F) d
    change w.valuation F (algebraMap (𝓞 F) F d) ≤ 1 at this
    rwa [hd, map_mul, hv, mul_one] at this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (t : w.adicCompletion F) ≤ 1
  rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/- English proof (translation)
Establish `key : ∀ r ∈ ((v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹), (fun i => (r • ((1 - singleV F v 1) * a)) ⊗ₜ[F] x i) ∈ latK Λ v (k + 1)`. Introduce `r hr`. Use `FractionalIdeal.mul_induction_on hr ?_ ?_` and prove the remaining obligations. Introduce `p hp t ht`. Take `⟨q, hq, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hp`.

Use `AddSubgroup.subset_closure ⟨t • ((1 - singleV F v 1) * a), ?_, algebraMap (𝓞 F) (𝓞 E) q • x, ?_, ?_⟩` and prove the remaining obligations. Introduce `w`. Rewrite using `[map_smul, map_mul, map_sub, map_one]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[ev_same, sub_self, zero_mul, smul_zero]`. Conclude with `zero_mem _`. Rewrite using `[ev_ne hw, sub_zero, one_mul, Algebra.smul_def]`. Conclude with `mul_mem (inv_int_away hw ht) (ha w)`. Rewrite using `[pow_succ', Ideal.map_mul, Submodule.mul_smul]`.

Conclude with `Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hq) hx`. Use function extensionality and compare the values at `i`. Rewrite using `[mul_smul, TensorProduct.smul_tmul]`. Use `congr 1`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`.

Introduce `r s hr hs`. Use `add_mem hr hs` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Rewrite using `[add_smul, TensorProduct.add_tmul]`.

Both sides reduce to the same expression. Use `key 1 (by` as an intermediate fact. Rewrite using `[FractionalIdeal.coe_ideal_mul_inv _ v.ne_bot]`. Conclude with `FractionalIdeal.one_mem_one _)`. Simplify `this` using `only [one_smul]`.
-/
theorem away_gen (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) {a : Af F}
    (ha : a ∈ intAf F) {x : Fin M → E}
    (hx : x ∈ (((v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E))) • Λ : Submodule (𝓞 E) (Fin M → E))) :
    (fun i => ((1 - singleV F v 1) * a) ⊗ₜ[F] x i) ∈ latK Λ v (k + 1) := by
  have key : ∀ r ∈ ((v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) *
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹),
      (fun i => (r • ((1 - singleV F v 1) * a)) ⊗ₜ[F] x i) ∈ latK Λ v (k + 1) := by
    intro r hr
    refine FractionalIdeal.mul_induction_on hr ?_ ?_
    · intro p hp t ht
      obtain ⟨q, hq, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hp
      refine AddSubgroup.subset_closure ⟨t • ((1 - singleV F v 1) * a), ?_,
        algebraMap (𝓞 F) (𝓞 E) q • x, ?_, ?_⟩
      · intro w
        rw [map_smul, map_mul, map_sub, map_one]
        by_cases hw : w = v
        · subst hw
          rw [ev_same, sub_self, zero_mul, smul_zero]; exact zero_mem _
        · rw [ev_ne hw, sub_zero, one_mul, Algebra.smul_def]
          exact mul_mem (inv_int_away hw ht) (ha w)
      · rw [pow_succ', Ideal.map_mul, Submodule.mul_smul]
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hq) hx
      · funext i
        rw [mul_smul, TensorProduct.smul_tmul]
        congr 1
        rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
    · intro r s hr hs
      have := add_mem hr hs
      convert this using 1
      funext i
      rw [add_smul, TensorProduct.add_tmul]; rfl
  have := key 1 (by
    rw [FractionalIdeal.coe_ideal_mul_inv _ v.ne_bot]
    exact FractionalIdeal.one_mem_one _)
  simpa only [one_smul] using this

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Simplify `away_gen Λ v k ha hx` using `only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Consider the case `zero => simp only [Pi.zero_apply, map_zero, mul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => simp only [Pi.add_apply, mul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => simp only [Pi.neg_apply, mul_neg]`. Conclude with `neg_mem hx`.
-/
theorem away_mem (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ)
    {z : Fin M → Af F ⊗[F] E} (hz : z ∈ latK Λ v k) :
    (fun i => ((1 - singleV F v 1) ⊗ₜ[F] (1 : E)) * z i) ∈ latK Λ v (k + 1) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, one_mul] using away_gen Λ v k ha hx
  | zero => simp only [Pi.zero_apply, map_zero, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, mul_neg]; exact neg_mem hx

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M J Λ v k h hk hl`. Use `⟨hk.1, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1` using `away_mem Λ v k (hk.2 y hy)`. Establish `h2` using `single_mem_latHat v _ (hl.2.2.2 _ (ev_mem_compLat v _ hy))`. Establish `h3 : _ ∈ latK Λ v (k + 1)` using `add_mem h2 h1`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Establish `e : (((locHom σ J v h : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) - 1) *ᵥ (fun i => Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (y i)) = fun i => Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (((finMat σ J h.1 - 1) *ᵥ y) i)`. Use function extensionality and compare the values at `j`. Rewrite using `[locHom_val, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]`.

Simplify using `[Matrix.mulVec, dotProduct]`. Rewrite using `[Pi.add_apply, e, ← idem_mul, ← add_mul, ← TensorProduct.add_tmul, add_sub_cancel, ← Algebra.TensorProduct.one_def, one_mul]`.
-/
theorem mem_congG_succ : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ), ∀ (h : GlobalTheory.Published.SUAdelic σ J), h ∈ GlobalTheory.TamCnt.congG σ J Λ v k → GlobalTheory.TamCnt.locHom σ J v h ∈ GlobalTheory.TamCnt.locCong σ J Λ v (k + 1) → h ∈ GlobalTheory.TamCnt.congG σ J Λ v (k + 1) := by
  intro F E _ _ _ _ _ σ M J Λ v k h hk hl
  refine ⟨hk.1, fun y hy => ?_⟩
  have h1 := away_mem Λ v k (hk.2 y hy)
  have h2 := single_mem_latHat v _ (hl.2.2.2 _ (ev_mem_compLat v _ hy))
  have h3 : _ ∈ latK Λ v (k + 1) := add_mem h2 h1
  convert h3 using 1
  funext i
  have e : (((locHom σ J v h : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) - 1) *ᵥ
      (fun i => Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (y i)) =
      fun i => Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (((finMat σ J h.1 - 1) *ᵥ y) i) := by
    funext j
    rw [locHom_val, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]
    simp [Matrix.mulVec, dotProduct]
  rw [Pi.add_apply, e, ← idem_mul, ← add_mul, ← TensorProduct.add_tmul, add_sub_cancel,
    ← Algebra.TensorProduct.one_def, one_mul]

end GlobalTheory.TamCnt.LevelUp
