import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKReal.Roots

variable (l : ℕ) [hl : Fact l.Prime]

/- English proof (translation)
Use `choose r hr using fun x : ℂ_[l] => IsAlgClosed.exists_pow_nat_eq x hl.out.pos`. Establish `hn : ∀ x : ℂ_[l], ‖x‖ ≤ 1 → ‖r x‖ ≤ 1` using `fun x hx => by`. Establish `h` using `congrArg norm (hr x)`. Rewrite `h` using `[norm_pow]`. Assume the negation of the conclusion as `h1`.

Conclude with `absurd (h ▸ one_lt_pow₀ (not_le.1 h1) hl.out.ne_zero) (not_lt.2 hx)`. Set `t : OC l → OC l` to `fun x => ⟨r x, (GlobalTheory.RingBasics.mem_OC _).2 (hn _ ((GlobalTheory.RingBasics.mem_OC _).1 x.2))⟩`. Conclude with `⟨fun n => t^[n] π, rfl, fun n => by show (t^[n + 1] π) ^ l = t^[n] π`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hr _)⟩`.
-/
theorem exists_roots (π : OC l) : ∃ s : ℕ → OC l, s 0 = π ∧ ∀ n, s (n + 1) ^ l = s n := by
  choose r hr using fun x : ℂ_[l] => IsAlgClosed.exists_pow_nat_eq x hl.out.pos
  have hn : ∀ x : ℂ_[l], ‖x‖ ≤ 1 → ‖r x‖ ≤ 1 := fun x hx => by
    have h := congrArg norm (hr x)
    rw [norm_pow] at h
    by_contra h1
    exact absurd (h ▸ one_lt_pow₀ (not_le.1 h1) hl.out.ne_zero) (not_lt.2 hx)
  let t : OC l → OC l := fun x => ⟨r x, (GlobalTheory.RingBasics.mem_OC _).2 (hn _ ((GlobalTheory.RingBasics.mem_OC _).1 x.2))⟩
  exact ⟨fun n => t^[n] π, rfl, fun n => by
    show (t^[n + 1] π) ^ l = t^[n] π
    rw [Function.iterate_succ_apply']
    exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hr _)⟩

variable {l} in

def flatOf (s : ℕ → OC l) (hs : ∀ n, s (n + 1) ^ l = s n) : OCb l :=
  (⟨fun n => Ideal.Quotient.mk _ (s n), fun n => by rw [← map_pow, hs]⟩ :
    Perfection (ModP (OC l) l) l)

variable {l} in

/- English proof (translation)
Establish `hp : ∀ n, s n ^ l ^ n = s 0` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ', pow_mul, hs, ih]`. Use `Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ⟨s n, rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[hp]`.
-/
theorem untilt_flatOf (s : ℕ → OC l) (hs : ∀ n, s (n + 1) ^ l = s n) : (flatOf s hs).untilt = s 0 := by
  have hp : ∀ n, s n ^ l ^ n = s 0 := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, hs, ih]
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ⟨s n, rfl, ?_⟩
  rw [hp]

end GlobalTheory.BKReal.Roots

namespace GlobalTheory.BKReal

/- English proof (translation)
Introduce `l hl a _ π hπ`. Take `⟨s, hs0, hs⟩` from `Roots.exists_roots l π`. Use `set fl := Roots.flatOf s hs`. Use `set t : Ainf l := WittVector.teichmuller l fl`. Establish `ht : Per.θ l t = π` using `(WittVector.fontaineTheta_teichmuller _).trans ((Roots.untilt_flatOf s hs).trans hs0)`.

Establish `htu : ¬ IsUnit t` using `fun h => hπ (ht ▸ h.map (Per.θ l))`. Establish `hc : IsAdicComplete (Ideal.span {t}) (Ainf l)` using `(GlobalTheory.Per.AinfComplete.main l _ htu).2`. Establish `hsep : ∀ x : Ainf l, (∀ n, t ^ n ∣ x) → x = 0` using `fun x h => GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (h n)`. Use `letI : Algebra (Wq l a) (Ainf l) := (wA l a).toRingHom.toAlgebra`. Take `⟨f, hfX⟩` from `GlobalTheory.Cyc.IoMap.algHom_exists (R := Wq l a) t (GlobalTheory.Per.AinfComplete.summ_of_precomplete _) hsep`.

Establish `hfC : ∀ w, f.toRingHom (C w) = wA l a w` using `f.commutes`. Establish `h1 : WittVector.frobenius t = t ^ l`. Rewrite using `[WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]`. Use `⟨fl, f.toRingHom, ht, hfX, hfC, fun x => ?_⟩` and prove the remaining obligations. Use `RingHom.congr_fun (ringHom_ext_of_sep (f.toRingHom.comp (frobS l a)) (WittVector.frobenius.comp f.toRingHom) (fun w => ?_) ?_ fun y hy => hsep y fun n => ?_) x` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply, frobS_C, hfC, wA_sigma]`. Simplify using `only [RingHom.comp_apply, frobS_X, map_pow]`. Rewrite using `[show f.toRingHom X = t from hfX, h1]`. Use `Dvd.dvd.trans ?_ (hy n)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, frobS_X, map_pow]`.

Rewrite using `[show f.toRingHom X = t from hfX]`. Conclude with `pow_dvd_pow_of_dvd (dvd_pow_self _ hl.out.ne_zero) n`.
-/
theorem exists_ev_of_root : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (π : OC l), ¬ IsUnit π →
    ∃ (fl : OCb l) (ev : (Wq l a)⟦X⟧ →+* Ainf l), Per.θ l (WittVector.teichmuller l fl) = π ∧
      ev X = WittVector.teichmuller l fl ∧ (∀ w, ev (C w) = wA l a w) ∧
      ∀ x, ev (frobS l a x) = WittVector.frobenius (ev x) := by
  intro l hl a _ π hπ
  obtain ⟨s, hs0, hs⟩ := Roots.exists_roots l π
  set fl := Roots.flatOf s hs
  set t : Ainf l := WittVector.teichmuller l fl
  have ht : Per.θ l t = π := (WittVector.fontaineTheta_teichmuller _).trans
    ((Roots.untilt_flatOf s hs).trans hs0)
  have htu : ¬ IsUnit t := fun h => hπ (ht ▸ h.map (Per.θ l))
  have hc : IsAdicComplete (Ideal.span {t}) (Ainf l) := (GlobalTheory.Per.AinfComplete.main l _ htu).2
  have hsep : ∀ x : Ainf l, (∀ n, t ^ n ∣ x) → x = 0 := fun x h =>
    GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (h n)
  letI : Algebra (Wq l a) (Ainf l) := (wA l a).toRingHom.toAlgebra
  obtain ⟨f, hfX⟩ := GlobalTheory.Cyc.IoMap.algHom_exists (R := Wq l a) t
    (GlobalTheory.Per.AinfComplete.summ_of_precomplete _) hsep
  have hfC : ∀ w, f.toRingHom (C w) = wA l a w := f.commutes
  have h1 : WittVector.frobenius t = t ^ l := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  refine ⟨fl, f.toRingHom, ht, hfX, hfC, fun x => ?_⟩
  refine RingHom.congr_fun (ringHom_ext_of_sep (f.toRingHom.comp (frobS l a))
    (WittVector.frobenius.comp f.toRingHom) (fun w => ?_) ?_ fun y hy => hsep y fun n => ?_) x
  · simp only [RingHom.comp_apply, frobS_C, hfC, wA_sigma]
  · simp only [RingHom.comp_apply, frobS_X, map_pow]
    rw [show f.toRingHom X = t from hfX, h1]
  · refine Dvd.dvd.trans ?_ (hy n)
    simp only [RingHom.comp_apply, frobS_X, map_pow]
    rw [show f.toRingHom X = t from hfX]
    exact pow_dvd_pow_of_dvd (dvd_pow_self _ hl.out.ne_zero) n

end GlobalTheory.BKReal
