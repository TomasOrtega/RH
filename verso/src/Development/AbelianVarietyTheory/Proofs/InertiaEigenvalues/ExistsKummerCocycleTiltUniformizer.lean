import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTeichmullerLogUnitBcrisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFix
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.FlatKummer

/- English proof (translation)
Establish `hp : ∀ k, ζ k ^ l ^ k = 1`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [h0]`. Consider the case `succ k ih => rw [pow_succ', pow_mul, hs, ih]`.

Establish `h1' : ∀ k, ζ (k + 1) ^ l ^ k = ζ 1`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', pow_mul, hs, ih]`.

Consider the cases of `m with`. Consider the case `zero => simp [h0]`. Consider the case `succ m`. Establish `h` using `orderOf_eq_prime_pow (x := ζ (m + 1)) (p := l) (n := m) (by rw [h1']; exact h1) (hp _)`. Rewrite using `[← h]`.

Conclude with `IsPrimitiveRoot.orderOf _`.
-/
theorem isPrimitiveRoot_of_seq {Ω : Type*} [Field Ω] (l : ℕ) [Fact l.Prime] (ζ : ℕ → Ω) (h0 : ζ 0 = 1)
    (hs : ∀ m, ζ (m + 1) ^ l = ζ m) (h1 : ζ 1 ≠ 1) (m : ℕ) : IsPrimitiveRoot (ζ m) (l ^ m) := by
  have hp : ∀ k, ζ k ^ l ^ k = 1 := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [pow_succ', pow_mul, hs, ih]
  have h1' : ∀ k, ζ (k + 1) ^ l ^ k = ζ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hs, ih]
  cases m with
  | zero => simp [h0]
  | succ m =>
    have h := orderOf_eq_prime_pow (x := ζ (m + 1)) (p := l) (n := m) (by rw [h1']; exact h1) (hp _)
    rw [← h]
    exact IsPrimitiveRoot.orderOf _

/- English proof (translation)
Establish `hne : ∀ m, NeZero (l ^ m)` using `fun m => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Establish `hiter : ∀ (x : ℕ → Ω), (∀ m, x (m + 1) ^ l = x m) → ∀ m, x m ^ l ^ m = x 0`. Introduce `x hx m`. Proceed by induction on `m with`. Consider the case `zero => simp`.

Consider the case `succ m ih => rw [pow_succ', pow_mul, hx, ih]`. Distinguish the cases in `hz0 : z 0 = 0`. Use `⟨0, fun m => ?_⟩` and prove the remaining obligations. Establish `a : z m = 0` using `pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 ((hiter z hz m).trans hz0)`. Establish `b : w m = 0` using `pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 ((hiter w hw m).trans (hwz.trans hz0))`.

Rewrite using `[a, b, mul_zero]`. Establish `hzm : ∀ m, z m ≠ 0` using `fun m h => hz0 (by rw [← hiter z hz m, h, zero_pow (hne m).out])`. Establish `hprim` using `isPrimitiveRoot_of_seq l ζ h0 hs h1`. Establish `hpow : ∀ m a b : ℕ, ζ m ^ a = ζ m ^ b ↔ (a : ZMod (l ^ m)) = (b : ZMod (l ^ m))`. Introduce `m a b`.

Establish `hf : IsOfFinOrder (ζ m)` using `(hprim m).isOfFinOrder (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)`. Rewrite using `[hf.pow_eq_pow_iff_modEq, ← (hprim m).eq_orderOf, ZMod.natCast_eq_natCast_iff]`. Establish `e1 : ∀ m, ∃ a : ℕ, w m = ζ m ^ a * z m`. Introduce `m`. Take `⟨a, -, ha⟩` from `(hprim m).eq_pow_of_pow_eq_one (ξ := w m / z m) (by`.

Rewrite using `[div_pow, hiter w hw, hiter z hz, hwz, div_self hz0])`. Conclude with `⟨a, by rw [ha, div_mul_cancel₀ _ (hzm m)]⟩`. Use `choose a ha using e1`. Establish `hd : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - (a i : ℤ)`. Introduce `i`.

Establish `h2` using `congrArg (· ^ l) (ha (i + 1))`. Simplify using `only [mul_pow, hw, hz] at h2`. Rewrite `h2` using `[← pow_mul, mul_comm (a (i + 1)), pow_mul, hs, ha i]`. Establish `h3` using `(hpow i _ _).mp (mul_right_cancel₀ (hzm i) h2)`. Rewrite `h3` using `[ZMod.natCast_eq_natCast_iff]`.

Conclude with `h3.dvd` after adjusting the coercions. Use `⟨PadicInt.ofIntSeq (fun i => (a i : ℤ)) (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ l hd), fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ l hd, ha m]`. Use `congr 1`. Rewrite using `[hpow]`.

Simplify using the standard rewrite rules.
-/
theorem exists_exponent_of_seq {Ω : Type*} [Field Ω] (l : ℕ) [Fact l.Prime] (ζ : ℕ → Ω) (h0 : ζ 0 = 1)
    (hs : ∀ m, ζ (m + 1) ^ l = ζ m) (h1 : ζ 1 ≠ 1) (z w : ℕ → Ω) (hz : ∀ m, z (m + 1) ^ l = z m)
    (hw : ∀ m, w (m + 1) ^ l = w m) (hwz : w 0 = z 0) :
    ∃ c : ℤ_[l], ∀ m, w m = ζ m ^ (PadicInt.toZModPow m c).val * z m := by
  have hne : ∀ m, NeZero (l ^ m) := fun m => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hiter : ∀ (x : ℕ → Ω), (∀ m, x (m + 1) ^ l = x m) → ∀ m, x m ^ l ^ m = x 0 := by
    intro x hx m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', pow_mul, hx, ih]
  by_cases hz0 : z 0 = 0
  · refine ⟨0, fun m => ?_⟩
    have a : z m = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 ((hiter z hz m).trans hz0)
    have b : w m = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1
      ((hiter w hw m).trans (hwz.trans hz0))
    rw [a, b, mul_zero]
  have hzm : ∀ m, z m ≠ 0 := fun m h => hz0 (by rw [← hiter z hz m, h, zero_pow (hne m).out])
  have hprim := isPrimitiveRoot_of_seq l ζ h0 hs h1
  have hpow : ∀ m a b : ℕ, ζ m ^ a = ζ m ^ b ↔ (a : ZMod (l ^ m)) = (b : ZMod (l ^ m)) := by
    intro m a b
    have hf : IsOfFinOrder (ζ m) := (hprim m).isOfFinOrder (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    rw [hf.pow_eq_pow_iff_modEq, ← (hprim m).eq_orderOf, ZMod.natCast_eq_natCast_iff]
  have e1 : ∀ m, ∃ a : ℕ, w m = ζ m ^ a * z m := by
    intro m
    obtain ⟨a, -, ha⟩ := (hprim m).eq_pow_of_pow_eq_one (ξ := w m / z m) (by
      rw [div_pow, hiter w hw, hiter z hz, hwz, div_self hz0])
    exact ⟨a, by rw [ha, div_mul_cancel₀ _ (hzm m)]⟩
  choose a ha using e1
  have hd : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - (a i : ℤ) := by
    intro i
    have h2 := congrArg (· ^ l) (ha (i + 1))
    simp only [mul_pow, hw, hz] at h2
    rw [← pow_mul, mul_comm (a (i + 1)), pow_mul, hs, ha i] at h2
    have h3 := (hpow i _ _).mp (mul_right_cancel₀ (hzm i) h2)
    rw [ZMod.natCast_eq_natCast_iff] at h3
    exact_mod_cast h3.dvd
  refine ⟨PadicInt.ofIntSeq (fun i => (a i : ℤ)) (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ l hd),
    fun m => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ l hd, ha m]
  congr 1
  rw [hpow]
  simp

/- English proof (translation)
Rewrite using `[rootT, rootT, Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]`.
-/
theorem rootT_succ_pow_l {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (m : ℕ) : rootT e (m + 1) ^ l = rootT e m := by
  rw [rootT, rootT, Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]

/- English proof (translation)
Introduce `l _ K bk C`. Take `⟨hz, -⟩` from `GlobalTheory.BSP.rootT_flat_alg_and_fix l K bk`. Use `choose z hz using hz`. Establish `hinj : Function.Injective (algebraMap (Om l) ℂ_[l])` using `(algebraMap (Om l) ℂ_[l]).injective`. Establish `hz' : ∀ n, ((rootT bk.flat n : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (z n)` using `hz`.

Establish `hzs : ∀ m, z (m + 1) ^ l = z m`. Introduce `m`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_pow, ← hz', ← hz', ← rootT_succ_pow_l bk.flat m]`. Use `push_cast`.

Both sides reduce to the same expression. Use `set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr`. Establish `hθ : rootT bk.flat 0 = intToOC K r` using `by show bk.flat.untilt = _`. Rewrite using `[← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]`. Conclude with `bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])`.

Establish `hz0 : z 0 = (((r : ↥K.1) : Om l))`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← hz', hθ, coe_intToOC]`. Both sides reduce to the same expression. Establish `good : ∀ g : ↥(GK K), ∃ c : ℤ_[l], ∀ m, rootT (Per.σF (g : GQ l) bk.flat) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT bk.flat m`.

Introduce `g`. Establish `hfix : (g : GQ l) (z 0) = z 0`. Rewrite using `[hz0]`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2`. Take `⟨c, hc⟩` from `exists_exponent_of_seq l C.ζ C.ζ_zero C.ζ_succ C.ζ_one z (fun m => (g : GQ l) (z m)) hzs (fun m => by rw [← map_pow, hzs]) hfix`.

Use `⟨c, fun m => ?_⟩` and prove the remaining obligations. Establish `hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF (g : GQ l) bk.flat) = Per.σF (g : GQ l) (((frobeniusEquiv (Per.Fl l) l).symm)^[k] bk.flat)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => rfl`.

Consider the case `succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]`. Establish `hsig : rootT (Per.σF (g : GQ l) bk.flat) m = Per.σO (g : GQ l) (rootT bk.flat m)`. Rewrite using `[rootT, hit, GlobalTheory.RingBasics.untilt_σF]`. Both sides reduce to the same expression. Rewrite using `[hsig]`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : ((Per.σO (g : GQ l) (rootT bk.flat m) : Per.OC l) : ℂ_[l]) = Per.σC (g : GQ l) (rootT bk.flat m : ℂ_[l])` using `by apply GlobalTheory.RingIface.sigO_coe`. Establish `h2 : Per.σC (g : GQ l) (algebraMap (Om l) ℂ_[l] (z m)) = algebraMap (Om l) ℂ_[l] ((g : GQ l) (z m))` using `GlobalTheory.RingBasics.σC_coe (g : GQ l) _`. Use `push_cast`. Rewrite using `[h1, hz', h2, hc m, map_mul, map_pow, C.ε_root]`.

Use `⟨fun g => if bk.FixFlat g then 0 else (good g).choose, fun g m => ?_, fun g hg => by simp [hg]⟩` and prove the remaining obligations. Distinguish the cases in `hg : bk.FixFlat g`. Simplify using `only [hg, if_true, map_zero, ZMod.val_zero, pow_zero, one_mul]`. Rewrite using `[show Per.σF (g : GQ l) bk.flat = bk.flat from hg]`. Simplify using `only [hg, if_false]`.

Conclude with `(good g).choose_spec m`.
-/
theorem exists_kummer_flat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), ∃ c : ↥(GK K) → ℤ_[l],
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) ∧ ∀ g, bk.FixFlat g → c g = 0 := by
  intro l _ K bk C
  obtain ⟨hz, -⟩ := GlobalTheory.BSP.rootT_flat_alg_and_fix l K bk
  choose z hz using hz
  have hinj : Function.Injective (algebraMap (Om l) ℂ_[l]) := (algebraMap (Om l) ℂ_[l]).injective
  have hz' : ∀ n, ((rootT bk.flat n : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (z n) := hz
  have hzs : ∀ m, z (m + 1) ^ l = z m := by
    intro m
    apply hinj
    rw [map_pow, ← hz', ← hz', ← rootT_succ_pow_l bk.flat m]
    push_cast
    rfl
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
  have hθ : rootT bk.flat 0 = intToOC K r := by
    show bk.flat.untilt = _
    rw [← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
    exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
  have hz0 : z 0 = (((r : ↥K.1) : Om l)) := by
    apply hinj
    rw [← hz', hθ, coe_intToOC]
    rfl
  have good : ∀ g : ↥(GK K), ∃ c : ℤ_[l], ∀ m, rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT bk.flat m := by
    intro g
    have hfix : (g : GQ l) (z 0) = z 0 := by
      rw [hz0]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2
    obtain ⟨c, hc⟩ := exists_exponent_of_seq l C.ζ C.ζ_zero C.ζ_succ C.ζ_one z (fun m => (g : GQ l) (z m)) hzs
      (fun m => by rw [← map_pow, hzs]) hfix
    refine ⟨c, fun m => ?_⟩
    have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF (g : GQ l) bk.flat) =
        Per.σF (g : GQ l) (((frobeniusEquiv (Per.Fl l) l).symm)^[k] bk.flat) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
    have hsig : rootT (Per.σF (g : GQ l) bk.flat) m = Per.σO (g : GQ l) (rootT bk.flat m) := by
      rw [rootT, hit, GlobalTheory.RingBasics.untilt_σF]; rfl
    rw [hsig]
    apply Subtype.ext
    have h1 : ((Per.σO (g : GQ l) (rootT bk.flat m) : Per.OC l) : ℂ_[l]) = Per.σC (g : GQ l) (rootT bk.flat m : ℂ_[l]) :=
      by apply GlobalTheory.RingIface.sigO_coe
    have h2 : Per.σC (g : GQ l) (algebraMap (Om l) ℂ_[l] (z m)) = algebraMap (Om l) ℂ_[l] ((g : GQ l) (z m)) :=
      GlobalTheory.RingBasics.σC_coe (g : GQ l) _
    push_cast
    rw [h1, hz', h2, hc m, map_mul, map_pow, C.ε_root]
  classical
  refine ⟨fun g => if bk.FixFlat g then 0 else (good g).choose, fun g m => ?_, fun g hg => by simp [hg]⟩
  by_cases hg : bk.FixFlat g
  · simp only [hg, if_true, map_zero, ZMod.val_zero, pow_zero, one_mul]
    rw [show Per.σF (g : GQ l) bk.flat = bk.flat from hg]
  · simp only [hg, if_false]
    exact (good g).choose_spec m

end GlobalTheory.FlatKummer

end
