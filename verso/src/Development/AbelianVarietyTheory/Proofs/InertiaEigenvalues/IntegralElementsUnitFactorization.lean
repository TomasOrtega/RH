import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueTiltInjectiveRetractStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityPropertiesStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace BridgeWittDvd

section Witt
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

/- English proof (translation)
Rewrite using `[← Ideal.mem_span_singleton]`. Conclude with `WittVector.mem_span_p_iff_coeff_zero_eq_zero x`.
-/
theorem dvd_iff (x : WittVector p k) : (p : WittVector p k) ∣ x ↔ x.coeff 0 = 0 := by
  rw [← Ideal.mem_span_singleton]
  exact WittVector.mem_span_p_iff_coeff_zero_eq_zero x

/- English proof (translation)
Establish `hc : IsAdicComplete (Ideal.span {(p : WittVector p k)}) (WittVector p k)` using `inferInstance`. Establish `key : ∀ (n : ℕ) (x y : WittVector p k), x ≡ y [SMOD (Ideal.span {(p : WittVector p k)} ^ n • ⊤ : Submodule (WittVector p k) (WittVector p k))] ↔ (p : WittVector p k) ^ n ∣ x - y`. Introduce `n x y`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Establish `step : ∀ m d : ℕ, (p : WittVector p k) ^ m ∣ w (m + d) - w m`.

Introduce `m d`. Proceed by induction on `d with`. Consider the case `zero => simp`. Consider the case `succ d ih`. Establish `e : w (m + (d + 1)) - w m = (w (m + d + 1) - w (m + d)) + (w (m + d) - w m)`.

Rewrite using `[← add_assoc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_add ((pow_dvd_pow _ (Nat.le_add_right m d)).trans (h _)) ih`. Take `⟨z, hz⟩` from `hc.toIsPrecomplete.prec (f := w) (fun {m n} hmn => by`.

Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Rewrite using `[key, ← dvd_neg, neg_sub]`. Conclude with `step m d)`. Use `⟨z, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[← dvd_neg, neg_sub]`.

Conclude with `(key n _ _).1 (hz n)`.
-/
theorem exists_limit (w : ℕ → WittVector p k) (h : ∀ n, (p : WittVector p k) ^ n ∣ w (n + 1) - w n) :
    ∃ z : WittVector p k, ∀ n, (p : WittVector p k) ^ n ∣ z - w n := by
  have hc : IsAdicComplete (Ideal.span {(p : WittVector p k)}) (WittVector p k) := inferInstance
  have key : ∀ (n : ℕ) (x y : WittVector p k),
      x ≡ y [SMOD (Ideal.span {(p : WittVector p k)} ^ n • ⊤ : Submodule (WittVector p k) (WittVector p k))] ↔
        (p : WittVector p k) ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have step : ∀ m d : ℕ, (p : WittVector p k) ^ m ∣ w (m + d) - w m := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have e : w (m + (d + 1)) - w m = (w (m + d + 1) - w (m + d)) + (w (m + d) - w m) := by
        rw [← add_assoc]; ring
      rw [e]
      exact dvd_add ((pow_dvd_pow _ (Nat.le_add_right m d)).trans (h _)) ih
  obtain ⟨z, hz⟩ := hc.toIsPrecomplete.prec (f := w) (fun {m n} hmn => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [key, ← dvd_neg, neg_sub]
    exact step m d)
  refine ⟨z, fun n => ?_⟩
  rw [← dvd_neg, neg_sub]
  exact (key n _ _).1 (hz n)

/- English proof (translation)
Establish `hd : ∀ n, ∃ c, PowerSeries.coeff n s = (p : WittVector p k) * c`. Introduce `n`. Apply `(dvd_iff _).2` to reduce the goal to its premises. Use `congrArg (PowerSeries.coeff n) h` as an intermediate fact. Simplify using `using this`.

Use `choose c hc using hd`. Use `⟨PowerSeries.mk c, ?_⟩` and prove the remaining obligations. Use `ext1 n`. Rewrite using `[← map_natCast (PowerSeries.C (R := WittVector p k)) p, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]`.
-/
theorem series_dvd (s : (WittVector p k)⟦X⟧)
    (h : PowerSeries.map (WittVector.constantCoeff (p := p) (R := k)) s = 0) :
    (p : (WittVector p k)⟦X⟧) ∣ s := by
  have hd : ∀ n, ∃ c, PowerSeries.coeff n s = (p : WittVector p k) * c := by
    intro n
    apply (dvd_iff _).2
    have := congrArg (PowerSeries.coeff n) h
    simpa using this
  choose c hc using hd
  refine ⟨PowerSeries.mk c, ?_⟩
  ext1 n
  rw [← map_natCast (PowerSeries.C (R := WittVector p k)) p, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

/- English proof (translation)
Take `⟨n, v, e⟩` from `WittVector.exists_eq_pow_p_mul' w h0`. Conclude with `⟨n, v, v.isUnit, e⟩`.
-/
theorem decomp (w : WittVector p k) (h0 : w ≠ 0) :
    ∃ (n : ℕ) (v : WittVector p k), IsUnit v ∧ w = (p : WittVector p k) ^ n * v := by
  obtain ⟨n, v, e⟩ := WittVector.exists_eq_pow_p_mul' w h0
  exact ⟨n, v, v.isUnit, e⟩
end Witt

/- English proof (translation)
Use `PerfectRing.ofSurjective F p fun x => ?_` and prove the remaining obligations. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := R) x`. Take `⟨a', rfl⟩` from `(bijective_frobenius R p).2 a`. Take `⟨b', rfl⟩` from `(bijective_frobenius R p).2 b`. Conclude with `⟨algebraMap R F a' / algebraMap R F b', by simp [frobenius_def, div_pow]⟩`.
-/
theorem perfect_frac (p : ℕ) [Fact p.Prime] (R F : Type) [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [CharP R p] [CharP F p] [PerfectRing R p] : PerfectRing F p := by
  refine PerfectRing.ofSurjective F p fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  obtain ⟨a', rfl⟩ := (bijective_frobenius R p).2 a
  obtain ⟨b', rfl⟩ := (bijective_frobenius R p).2 b
  exact ⟨algebraMap R F a' / algebraMap R F b', by simp [frobenius_def, div_pow]⟩

end BridgeWittDvd

/- English proof (translation)
Introduce `l _ K bk`. Use `haveI : PerfectRing (Cb l) l := BridgeWittDvd.perfect_frac l (OCb l) (Cb l)`. Take `⟨ek, -, hek, hinj, -, -⟩` from `GlobalTheory.T.exists_residueTilt_injective_retract l K bk`. Take `⟨-, hS, hX, -, -⟩` from `GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk`. Take `⟨hsat, hcl, hφ, hgal, hunit⟩` from `GlobalTheory.T.breuilKisin_OE_stability_properties l K bk`.

Establish `hsatn : ∀ (n : ℕ) (v : WCb l), ((l : ℕ) : WCb l) ^ n * v ∈ bk.OE → v ∈ bk.OE`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro v hv`. Simplify using `using hv`.

Consider the case `succ n ih`. Introduce `v hv`. Rewrite `hv` using `[pow_succ, mul_assoc]`. Conclude with `hsat v (ih _ hv)`. Use `⟨?_, hunit _ (hS _) hX, ?_, ?_, ?_, hgal, hφ⟩` and prove the remaining obligations.

Introduce and unpack `w hw ⟨v, rfl⟩`. Conclude with `⟨v, hsat v hw, rfl⟩`. Introduce `s hs`. Use `hunit _ (hS s) (WittVector.isUnit_of_coeff_zero_ne_zero _ fun h0 => hs ?_)` and prove the remaining obligations. Apply `BridgeWittDvd.series_dvd` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[hek, map_zero]`. Establish `e : (bk.evW s).coeff 0 = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0)` using `rfl`. Rewrite `h0` using `[e]`. Conclude with `(FaithfulSMul.algebraMap_injective (OCb l) (Cb l)) (h0.trans (map_zero _).symm)`.

Introduce `w hw h0`. Take `⟨n, v, hv, e⟩` from `BridgeWittDvd.decomp (p := l) (k := Cb l) w h0`. Establish `hvO : v ∈ bk.OE` using `hsatn n v (e ▸ hw)`. Take `⟨v', hv', e'⟩` from `hunit v hvO hv`. Conclude with `⟨n, v, v', hvO, hv', e', e⟩`.

Introduce `w hw h`. Take `⟨z, hz⟩` from `BridgeWittDvd.exists_limit (p := l) (k := Cb l) w h`. Conclude with `⟨z, hcl z fun n => ⟨w n, hw n, hz n⟩, hz⟩`.
-/
theorem Bridge.kisin_reduction_unit_at_uniformizer : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (K : Formalism.BasicNotions.Loc.FinExt l) (bk : GlobalTheory.BSP.BK K), (∀ w ∈ bk.OE, l.cast ∣ w → ∃ v ∈ bk.OE, w = l.cast * v) ∧ (∃ w ∈ bk.OE, HMul.hMul (α := Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (β := fun (x : bk.S) ↦ Formalism.BasicNotions.Loc.WCb l) bk.evW PowerSeries.X : Formalism.BasicNotions.Loc.WCb l) w = OfNat.ofNat 1) ∧ (∀ (s : bk.S), ¬l.cast ∣ s → ∃ w ∈ bk.OE, HMul.hMul (α := Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (β := fun (x : bk.S) ↦ Formalism.BasicNotions.Loc.WCb l) bk.evW s : Formalism.BasicNotions.Loc.WCb l) w = OfNat.ofNat 1) ∧ (∀ w ∈ bk.OE, w ≠ OfNat.ofNat 0 → ∃ (k : ℕ) (v : Formalism.BasicNotions.Loc.WCb l) (v' : Formalism.BasicNotions.Loc.WCb l), v ∈ bk.OE ∧ v' ∈ bk.OE ∧ v * v' = OfNat.ofNat 1 ∧ w = HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast k * v) ∧ (∀ (w : ℕ → Formalism.BasicNotions.Loc.WCb l), (∀ (n : ℕ), w n ∈ bk.OE) → (∀ (n : ℕ), HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast n ∣ w (n + OfNat.ofNat 1) - w n) → ∃ z ∈ bk.OE, ∀ (n : ℕ), HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast n ∣ z - w n) ∧ (∀ (g : ↥(Formalism.BasicNotions.Loc.GK K)), bk.FixFlat g → ∀ w ∈ bk.OE, DFunLike.coe (F := Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.WCb l) ↦ Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (F := Formalism.BasicNotions.Loc.GQ l →* Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.GQ l) ↦ Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (GlobalTheory.Prism.galW l) (g.val (p := fun (x : Formalism.BasicNotions.Loc.GQ l) ↦ x ∈ Formalism.BasicNotions.Loc.GK K)) : Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) w = w) ∧ ∀ w ∈ bk.OE, Membership.mem (α := Formalism.BasicNotions.Loc.WCb l) bk.OE (DFunLike.coe (F := Formalism.BasicNotions.Loc.WCb l →ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.WCb l) ↦ Formalism.BasicNotions.Loc.WCb l) (Formalism.BasicNotions.Loc.frobW l) w : Formalism.BasicNotions.Loc.WCb l) := by
  intro l _ K bk
  haveI : PerfectRing (Cb l) l := BridgeWittDvd.perfect_frac l (OCb l) (Cb l)
  obtain ⟨ek, -, hek, hinj, -, -⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  obtain ⟨-, hS, hX, -, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨hsat, hcl, hφ, hgal, hunit⟩ := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  have hsatn : ∀ (n : ℕ) (v : WCb l), ((l : ℕ) : WCb l) ^ n * v ∈ bk.OE → v ∈ bk.OE := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, mul_assoc] at hv
      exact hsat v (ih _ hv)
  refine ⟨?_, hunit _ (hS _) hX, ?_, ?_, ?_, hgal, hφ⟩
  · rintro w hw ⟨v, rfl⟩
    exact ⟨v, hsat v hw, rfl⟩
  · intro s hs
    refine hunit _ (hS s) (WittVector.isUnit_of_coeff_zero_ne_zero _ fun h0 => hs ?_)
    apply BridgeWittDvd.series_dvd
    apply hinj
    rw [hek, map_zero]
    have e : (bk.evW s).coeff 0 = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := rfl
    rw [e] at h0
    exact (FaithfulSMul.algebraMap_injective (OCb l) (Cb l)) (h0.trans (map_zero _).symm)
  · intro w hw h0
    obtain ⟨n, v, hv, e⟩ := BridgeWittDvd.decomp (p := l) (k := Cb l) w h0
    have hvO : v ∈ bk.OE := hsatn n v (e ▸ hw)
    obtain ⟨v', hv', e'⟩ := hunit v hvO hv
    exact ⟨n, v, v', hvO, hv', e', e⟩
  · intro w hw h
    obtain ⟨z, hz⟩ := BridgeWittDvd.exists_limit (p := l) (k := Cb l) w h
    exact ⟨z, hcl z fun n => ⟨w n, hw n, hz n⟩, hz⟩

namespace GlobalTheory.OEDvr

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Use `PerfectRing.ofSurjective _ _ fun x => ?_` and prove the remaining obligations. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := OCb l) x`. Use `⟨algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm a) / algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm b), ?_⟩` and prove the remaining obligations. Rewrite using `[frobenius_def, div_pow, ← map_pow (algebraMap (OCb l) (Cb l)), ← map_pow (algebraMap (OCb l) (Cb l)), frobeniusEquiv_symm_pow_p, frobeniusEquiv_symm_pow_p]`.
-/
theorem perfectRing_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  refine ⟨algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm a) /
    algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm b), ?_⟩
  rw [frobenius_def, div_pow, ← map_pow (algebraMap (OCb l) (Cb l)),
    ← map_pow (algebraMap (OCb l) (Cb l)), frobeniusEquiv_symm_pow_p,
    frobeniusEquiv_symm_pow_p]

variable {K : FinExt l} (bk : BK K)

/- English proof (translation)
The claim follows from `Bridge.kisin_reduction_unit_at_uniformizer`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w ∈ bk.OE, ((l : ℕ) : WCb l) ∣ w → ∃ v ∈ bk.OE, w = (l : WCb l) * v) ∧ (∃ w ∈ bk.OE, bk.evW X * w = 1) ∧ (∀ s : bk.S, ¬ (l : bk.S) ∣ s → ∃ w ∈ bk.OE, bk.evW s * w = 1) ∧ (∀ w ∈ bk.OE, w ≠ 0 → ∃ (k : ℕ) (v v' : WCb l), v ∈ bk.OE ∧ v' ∈ bk.OE ∧ v * v' = 1 ∧ w = (l : WCb l) ^ k * v) ∧ (∀ w : ℕ → WCb l, (∀ n, w n ∈ bk.OE) → (∀ n, (l : WCb l) ^ n ∣ w (n + 1) - w n) → ∃ z ∈ bk.OE, ∀ n, (l : WCb l) ^ n ∣ z - w n) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) :=
  Bridge.kisin_reduction_unit_at_uniformizer

end GlobalTheory.OEDvr
