import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffEqMkRootT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSumFactorial
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Pst.NoLog

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use `haveI := K.2`. Use `haveI : Finite (GQ l ⧸ GK K) := Subgroup.quotient_finite_of_isOpen _ K.1.fixingSubgroup_isOpen`. Use `haveI := Fintype.ofFinite (GQ l ⧸ GK K)`. Set `F : GQ l → P.R.B` to `fun g => P.actQ g b - (kummer P g : ℚ_[l]) • P.tB`. Establish `h1 : ∀ s g, P.actQ s (F g) = F (s * g) + (kummer P s : ℚ_[l]) • P.tB` using `fun s g => by`.

Simplify using `only [F, map_sub, map_smul, map_mul, AlgEquiv.mul_apply, localPrime_galoisAction_periodT, kummer_mul, add_smul, smul_smul, mul_comm]`. Normalize the expressions using the abelian group laws. Establish `h2 : ∀ g (h : ↥(GK K)), F (g * h) = F g` using `fun g h => by`. Establish `e : F h = b` using `by simp only [F, ← hb h h.2]; abel`. Use `h1 g h` as an intermediate fact.

Rewrite `this` using `[e]`. Conclude with `(sub_eq_iff_eq_add.2 this).symm`. Establish `h3 : ∀ g, F (QuotientGroup.mk g : GQ l ⧸ GK K).out = F g` using `fun g => by`. Take `⟨h, e⟩` from `QuotientGroup.mk_out_eq_mul (GK K) g`. Rewrite using `[e, h2]`.

Establish `hn : ((Fintype.card (GQ l ⧸ GK K) : ℕ) : ℚ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Use `⟨((Fintype.card (GQ l ⧸ GK K) : ℕ) : ℚ_[l])⁻¹ • ∑ q : GQ l ⧸ GK K, F q.out, fun s => ?_⟩` and prove the remaining obligations. Establish `h4 : ∑ q : GQ l ⧸ GK K, F (s * q.out) = ∑ q : GQ l ⧸ GK K, F q.out` using `Fintype.sum_equiv (MulAction.toPerm s) _ _ fun q => by`. Rewrite using `[MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, h3, smul_eq_mul]`. Rewrite using `[map_smul, map_sum, ← smul_sub]`.

Simplify using `only [h1]`. Rewrite using `[Finset.sum_add_distrib, h4, add_sub_cancel_left, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ hn, one_smul]`.
-/
theorem exists_full (P : LocPrime l) (K : FinExt l) (b : P.R.B)
    (hb : ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB) :
    ∃ b' : P.R.B, ∀ g : GQ l, P.actQ g b' - b' = (kummer P g : ℚ_[l]) • P.tB := by
  haveI := K.2
  haveI : Finite (GQ l ⧸ GK K) := Subgroup.quotient_finite_of_isOpen _ K.1.fixingSubgroup_isOpen
  haveI := Fintype.ofFinite (GQ l ⧸ GK K)
  let F : GQ l → P.R.B := fun g => P.actQ g b - (kummer P g : ℚ_[l]) • P.tB
  have h1 : ∀ s g, P.actQ s (F g) = F (s * g) + (kummer P s : ℚ_[l]) • P.tB := fun s g => by
    simp only [F, map_sub, map_smul, map_mul, AlgEquiv.mul_apply, localPrime_galoisAction_periodT, kummer_mul, add_smul, smul_smul,
      mul_comm]
    abel
  have h2 : ∀ g (h : ↥(GK K)), F (g * h) = F g := fun g h => by
    have e : F h = b := by simp only [F, ← hb h h.2]; abel
    have := h1 g h
    rw [e] at this
    exact (sub_eq_iff_eq_add.2 this).symm
  have h3 : ∀ g, F (QuotientGroup.mk g : GQ l ⧸ GK K).out = F g := fun g => by
    obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul (GK K) g
    rw [e, h2]
  have hn : ((Fintype.card (GQ l ⧸ GK K) : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨((Fintype.card (GQ l ⧸ GK K) : ℕ) : ℚ_[l])⁻¹ • ∑ q : GQ l ⧸ GK K, F q.out, fun s => ?_⟩
  have h4 : ∑ q : GQ l ⧸ GK K, F (s * q.out) = ∑ q : GQ l ⧸ GK K, F q.out :=
    Fintype.sum_equiv (MulAction.toPerm s) _ _ fun q => by
      rw [MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, h3, smul_eq_mul]
  rw [map_smul, map_sum, ← smul_sub]
  simp only [h1]
  rw [Finset.sum_add_distrib, h4, add_sub_cancel_left, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ hn, one_smul]

section Log

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

/- English proof (translation)
Use `haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Establish `he1 : e.untilt = 1` using `Subtype.ext (by`. Use `hr 0` as an intermediate fact. Rewrite `this` using `[C.ζ_zero, one_pow, map_one]`. Conclude with `this)`.

Establish `hrm` using `hr m`. Use `set a := (PadicInt.toZModPow m d).val with ha`. Take `⟨b, hb⟩ : ∃ b, a + b = l ^ m` from `Nat.exists_eq_add_of_le (ZMod.val_lt _).le |>.imp fun _ h => h.symm`. Use `set em := ((frobeniusEquiv (Per.Fl l) l).symm)^[m] C.ε with hem`. Use `set fm := ((frobeniusEquiv (Per.Fl l) l).symm)^[m] e with hfm`.

Establish `hε` using `TAct.eps_untilt C`. Establish `hr1 : ((em.untilt : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (C.ζ m)` using `C.ε_root m`. Establish `hr2 : ((fm.untilt : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (C.ζ m ^ a)` using `hrm`. Establish `he : (fm * em ^ b).untilt = 1`. Rewrite using `[map_mul, map_pow]`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[hr1, hr2, ← map_pow, ← map_mul, ← pow_add, hb, TAct.zeta_pow, map_one]`. Take `⟨z, _, hz, -, -⟩` from `exists_isLogA l _ he`. Establish `h1` using `TAct.logA_pow C.j_cris he hz (l ^ m)`.

Establish `h2` using `TAct.logA_mul C.j_cris he1 (by rw [map_pow, hε, one_pow]) hy (TAct.logA_pow C.j_cris hε C.t_log b)`. Establish `h3 : (fm * em ^ b) ^ (l ^ m) = e * C.ε ^ b`. Rewrite using `[mul_pow, ← pow_mul, mul_comm b, pow_mul, hem, hfm, TAct.iter_pow, TAct.iter_pow]`. Rewrite `h1` using `[h3]`. Establish `h4` using `(LogFun.log_fun l _ _ (by rw [map_mul, he1, map_pow, hε, one_pow, one_mul]) h1).1 _ h2`.

Use `⟨z - C.t, ?_⟩` and prove the remaining obligations. Establish `h5 : (a : Per.Acris l) + b = (l : Per.Acris l) ^ m`. Conclude with `congrArg (Nat.cast : ℕ → Per.Acris l) hb` after adjusting the coercions. Move the coercions through the operations in `at h4`. Take the linear combination `h4 - C.t * h5`.
-/
theorem log_cong (C : Core l) (e : Per.Fl l) (d : ℤ_[l]) (y : Per.Acris l)
    (hr : ∀ m : ℕ, (rootT e m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (C.ζ m ^ (PadicInt.toZModPow m d).val))
    (hy : IsLogA e y) (m : ℕ) : ∃ w : Per.Acris l,
    y - ((PadicInt.toZModPow m d).val : Per.Acris l) * C.t = (l : Per.Acris l) ^ m * w := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have he1 : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [C.ζ_zero, one_pow, map_one] at this
    exact this)
  have hrm := hr m
  set a := (PadicInt.toZModPow m d).val with ha
  obtain ⟨b, hb⟩ : ∃ b, a + b = l ^ m := Nat.exists_eq_add_of_le (ZMod.val_lt _).le |>.imp fun _ h => h.symm
  set em := ((frobeniusEquiv (Per.Fl l) l).symm)^[m] C.ε with hem
  set fm := ((frobeniusEquiv (Per.Fl l) l).symm)^[m] e with hfm
  have hε := TAct.eps_untilt C
  have hr1 : ((em.untilt : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (C.ζ m) := C.ε_root m
  have hr2 : ((fm.untilt : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (C.ζ m ^ a) := hrm
  have he : (fm * em ^ b).untilt = 1 := by
    rw [map_mul, map_pow]
    apply Subtype.ext
    push_cast
    rw [hr1, hr2, ← map_pow, ← map_mul, ← pow_add, hb, TAct.zeta_pow, map_one]
  obtain ⟨z, _, hz, -, -⟩ := exists_isLogA l _ he
  have h1 := TAct.logA_pow C.j_cris he hz (l ^ m)
  have h2 := TAct.logA_mul C.j_cris he1 (by rw [map_pow, hε, one_pow]) hy
    (TAct.logA_pow C.j_cris hε C.t_log b)
  have h3 : (fm * em ^ b) ^ (l ^ m) = e * C.ε ^ b := by
    rw [mul_pow, ← pow_mul, mul_comm b, pow_mul, hem, hfm, TAct.iter_pow, TAct.iter_pow]
  rw [h3] at h1
  have h4 := (LogFun.log_fun l _ _ (by rw [map_mul, he1, map_pow, hε, one_pow, one_mul]) h1).1 _ h2
  refine ⟨z - C.t, ?_⟩
  have h5 : (a : Per.Acris l) + b = (l : Per.Acris l) ^ m := by
    exact_mod_cast congrArg (Nat.cast : ℕ → Per.Acris l) hb
  push_cast at h4
  linear_combination h4 - C.t * h5

/- English proof (translation)
Use `haveI := (acris_basic l).1`. Rewrite using `[IsHausdorff.eq_iff_smodEq (I := Ideal.span {(l : Per.Acris l)})]`. Introduce `m`. Take `⟨w, hw⟩` from `log_cong C e x y hr hy m`. Use `haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`.

Establish `hk : x - ((PadicInt.toZModPow m x).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m))`. Rewrite using `[RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]`. Rewrite `hk` using `[PadicInt.ker_toZModPow, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `hk`. Establish `hc'` using `congrArg ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) hc`.

Rewrite `hc'` using `[map_mul, map_sub, map_pow, map_natCast, map_natCast, RingHom.comp_apply, RingHom.comp_apply]`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Use `⟨w - algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c) * C.t, ?_⟩` and prove the remaining obligations. Take the linear combination `- hw - C.t * hc'`.
-/
theorem log_eq (C : Core l) (e : Per.Fl l) (x : ℤ_[l]) (y : Per.Acris l)
    (hr : ∀ m : ℕ, (rootT e m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (C.ζ m ^ (PadicInt.toZModPow m x).val))
    (hy : IsLogA e y) : y = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l x) * C.t := by
  haveI := (acris_basic l).1
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(l : Per.Acris l)})]
  intro m
  obtain ⟨w, hw⟩ := log_cong C e x y hr hy m
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hk : x - ((PadicInt.toZModPow m x).val : ℤ_[l]) ∈
      RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  have hc' := congrArg ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) hc
  rw [map_mul, map_sub, map_pow, map_natCast, map_natCast, RingHom.comp_apply, RingHom.comp_apply] at hc'
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨w - algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c) * C.t, ?_⟩
  linear_combination - hw - C.t * hc'

end Log

def IsLogP (w : Per.AinfP l) (y : Per.BdRp l) : Prop :=
  ∀ n : ℕ, ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) * Per.ev l n y =
    Ideal.Quotient.mk _ (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * w ^ (k + 1))

/- English proof (translation)
Use `GlobalTheory.RingIface.ev_ext l _ _ fun n => ?_` and prove the remaining obligations. Set `q : Per.AinfP l →+* Per.AinfP l ⧸ Per.kerP l ^ n` to `Ideal.Quotient.mk _`. Establish `hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : Per.AinfP l ⧸ Per.kerP l ^ n)` using `fun m hm => by`. Use `(GlobalTheory.RingBasics.isUnit_nat l m hm).map q` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Apply `(hR _ n.factorial_ne_zero).mul_left_cancel` to reduce the goal to its premises. Rewrite using `[map_add, mul_add, hy n, hy' n, hz n]`. Establish `hI : ((Per.kerP l).map q) ^ n = ⊥`. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.map_quotient_self _`.

Establish `key` using `LogAdd.trunc_add hR n _ hI _ _ (Ideal.mem_map_of_mem q ha) (Ideal.mem_map_of_mem q hb)`. Express the relevant statement in the definitionally equal form `q _ = q _ + q _`. Simplify using `only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, map_add]`. Conclude with `key`.
-/
theorem IsLogP.add {a b : Per.AinfP l} {y y' z : Per.BdRp l} (ha : a ∈ Per.kerP l) (hb : b ∈ Per.kerP l)
    (hy : IsLogP a y) (hy' : IsLogP b y') (hz : IsLogP (a + b + a * b) z) : z = y + y' := by
  refine GlobalTheory.RingIface.ev_ext l _ _ fun n => ?_
  let q : Per.AinfP l →+* Per.AinfP l ⧸ Per.kerP l ^ n := Ideal.Quotient.mk _
  have hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : Per.AinfP l ⧸ Per.kerP l ^ n) := fun m hm => by
    have := (GlobalTheory.RingBasics.isUnit_nat l m hm).map q
    rwa [map_natCast] at this
  apply (hR _ n.factorial_ne_zero).mul_left_cancel
  rw [map_add, mul_add, hy n, hy' n, hz n]
  have hI : ((Per.kerP l).map q) ^ n = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  have key := LogAdd.trunc_add hR n _ hI _ _ (Ideal.mem_map_of_mem q ha) (Ideal.mem_map_of_mem q hb)
  change q _ = q _ + q _
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, map_add]
  exact key

/- English proof (translation)
Introduce `n`. Establish `h` using `hy n`. Rewrite `h` using `[← map_natCast (Per.ev l n), ← map_mul]`. Establish `h2` using `CrisUnique.ev_σDp g n _ _ h`. Rewrite `h2` using `[map_mul, map_natCast, map_mul, map_natCast]`.

Rewrite using `[h2]`. Simplify using `only [map_sum (Per.extP (Per.σA g)), map_mul (Per.extP (Per.σA g)), map_pow (Per.extP (Per.σA g)), map_neg (Per.extP (Per.σA g)), map_one (Per.extP (Per.σA g)), map_natCast (Per.extP (Per.σA g))]`.
-/
theorem IsLogP.gal {a : Per.AinfP l} {y : Per.BdRp l} (hy : IsLogP a y) (g : GQ l) :
    IsLogP (Per.extP (Per.σA g) a) (Per.σDp g y) := by
  intro n
  have h := hy n
  rw [← map_natCast (Per.ev l n), ← map_mul] at h
  have h2 := CrisUnique.ev_σDp g n _ _ h
  rw [map_mul, map_natCast, map_mul, map_natCast] at h2
  rw [h2]
  simp only [map_sum (Per.extP (Per.σA g)), map_mul (Per.extP (Per.σA g)), map_pow (Per.extP (Per.σA g)),
    map_neg (Per.extP (Per.σA g)), map_one (Per.extP (Per.σA g)), map_natCast (Per.extP (Per.σA g))]

/- English proof (translation)
Establish `hmem : ∀ m, algebraMap (Om l) ℂ_[l] (ν m) ∈ PadicComplexInt l` using `fun m => by`. Establish `h : algebraMap (Om l) ℂ_[l] (ν m) ^ l ^ m = u`. Use `zeta_pow_iter hs 0 m` as an intermediate fact. Rewrite `this` using `[zero_add, h0]`. Rewrite using `[← map_pow, this, map_natCast]`.

Establish `h2 : Valued.v (algebraMap (Om l) ℂ_[l] (ν m)) ^ l ^ m ≤ 1`. Rewrite using `[← map_pow, h]`. Conclude with `natCast_mem (PadicComplexInt l) u`. Conclude with `(pow_le_one_iff_of_nonneg zero_le (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 h2`. Take `⟨e, he⟩` from `zeta_exists_tilt (p := l) (O := Per.OC l) (fun m => ⟨algebraMap (Om l) ℂ_[l] (ν m), hmem m⟩) (fun m => Subtype.ext (by show algebraMap (Om l) ℂ_[l] (ν (m + 1)) ^ l = algebraMap (Om l) ℂ_[l] (ν m)`.

Rewrite using `[← map_pow, hs]))`. Conclude with `⟨e, fun m => congrArg Subtype.val (he m)⟩`.
-/
theorem exists_tilt (ν : ℕ → Om l) (hs : ∀ m, ν (m + 1) ^ l = ν m) (u : ℕ) (h0 : ν 0 = u) :
    ∃ e : Per.Fl l, ∀ m, (rootT e m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ν m) := by
  have hmem : ∀ m, algebraMap (Om l) ℂ_[l] (ν m) ∈ PadicComplexInt l := fun m => by
    have h : algebraMap (Om l) ℂ_[l] (ν m) ^ l ^ m = u := by
      have := zeta_pow_iter hs 0 m
      rw [zero_add, h0] at this
      rw [← map_pow, this, map_natCast]
    have h2 : Valued.v (algebraMap (Om l) ℂ_[l] (ν m)) ^ l ^ m ≤ 1 := by
      rw [← map_pow, h]
      exact natCast_mem (PadicComplexInt l) u
    exact (pow_le_one_iff_of_nonneg zero_le (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 h2
  obtain ⟨e, he⟩ := zeta_exists_tilt (p := l) (O := Per.OC l)
    (fun m => ⟨algebraMap (Om l) ℂ_[l] (ν m), hmem m⟩) (fun m => Subtype.ext (by
      show algebraMap (Om l) ℂ_[l] (ν (m + 1)) ^ l = algebraMap (Om l) ℂ_[l] (ν m)
      rw [← map_pow, hs]))
  exact ⟨e, fun m => congrArg Subtype.val (he m)⟩

/- English proof (translation)
Establish `hne : ∀ m, NeZero (l ^ m)` using `fun m => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Establish `hp : ∀ m, ν m ^ l ^ m = u` using `fun m => by`. Use `zeta_pow_iter hs 0 m` as an intermediate fact. Rewrite `this` using `[zero_add, h0]`. Then use the resulting hypothesis. Establish `hν : ∀ m, ν m ≠ 0` using `fun m h => by`.

Use `hp m` as an intermediate fact. Rewrite `this` using `[h, zero_pow (hne m).out]`. Conclude with `Nat.cast_ne_zero.2 hu this.symm`. Establish `h1 : ∀ m, ∃ a : ℕ, g (ν m) = P.ζQ m ^ a * ν m`. Introduce `m`.

Take `⟨a, -, ha⟩` from `(isPrimitiveRoot_zeta P m).eq_pow_of_pow_eq_one (ξ := g (ν m) / ν m) (by rw [div_pow, ← map_pow, hp, map_natCast, div_self (Nat.cast_ne_zero.mpr hu)])`. Conclude with `⟨a, by rw [ha, div_mul_cancel₀ _ (hν m)]⟩`. Use `choose a ha using h1`. Establish `hd : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - (a i : ℤ)`. Introduce `i`.

Establish `h2` using `congrArg (· ^ l) (ha (i + 1))`. Simplify using `only [← map_pow, mul_pow, hs] at h2`. Rewrite `h2` using `[← pow_mul, mul_comm (a (i + 1)), pow_mul, P.ζQ_succ, ha i]`. Establish `h3` using `(zeta_pow_eq_iff P i _ _).mp (mul_right_cancel₀ (hν i) h2)`. Rewrite `h3` using `[ZMod.natCast_eq_natCast_iff]`.

Conclude with `h3.dvd` after adjusting the coercions. Use `⟨PadicInt.ofIntSeq (fun i => (a i : ℤ)) (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ l hd), fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ l hd, ha m]`. Use `congr 1`. Rewrite using `[zeta_pow_eq_iff]`.

Simplify using the standard rewrite rules.
-/
theorem exists_exponent (P : LocPrime l) (ν : ℕ → Om l) (hs : ∀ m, ν (m + 1) ^ l = ν m) (u : ℕ) (hu : u ≠ 0)
    (h0 : ν 0 = u) (g : GQ l) :
    ∃ c : ℤ_[l], ∀ m, g (ν m) = P.ζQ m ^ (PadicInt.toZModPow m c).val * ν m := by
  have hne : ∀ m, NeZero (l ^ m) := fun m => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hp : ∀ m, ν m ^ l ^ m = u := fun m => by
    have := zeta_pow_iter hs 0 m
    rwa [zero_add, h0] at this
  have hν : ∀ m, ν m ≠ 0 := fun m h => by
    have := hp m
    rw [h, zero_pow (hne m).out] at this
    exact Nat.cast_ne_zero.2 hu this.symm
  have h1 : ∀ m, ∃ a : ℕ, g (ν m) = P.ζQ m ^ a * ν m := by
    intro m
    obtain ⟨a, -, ha⟩ := (isPrimitiveRoot_zeta P m).eq_pow_of_pow_eq_one
      (ξ := g (ν m) / ν m) (by rw [div_pow, ← map_pow, hp, map_natCast, div_self (Nat.cast_ne_zero.mpr hu)])
    exact ⟨a, by rw [ha, div_mul_cancel₀ _ (hν m)]⟩
  choose a ha using h1
  have hd : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - (a i : ℤ) := by
    intro i
    have h2 := congrArg (· ^ l) (ha (i + 1))
    simp only [← map_pow, mul_pow, hs] at h2
    rw [← pow_mul, mul_comm (a (i + 1)), pow_mul, P.ζQ_succ, ha i] at h2
    have h3 := (zeta_pow_eq_iff P i _ _).mp (mul_right_cancel₀ (hν i) h2)
    rw [ZMod.natCast_eq_natCast_iff] at h3
    exact_mod_cast h3.dvd
  refine ⟨PadicInt.ofIntSeq (fun i => (a i : ℤ)) (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ l hd),
    fun m => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ l hd, ha m]
  congr 1
  rw [zeta_pow_eq_iff]
  simp

/- English proof (translation)
Use `Perfection.ext fun n => ?_` and prove the remaining obligations. Use `(GlobalTheory.AdicMaps.coeff_galois l g x n (rootT x n) (coeff_eq_mk_rootT x n)).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = PreTilt.coeff n (x * e)`. Rewrite using `[map_mul, coeff_eq_mk_rootT, coeff_eq_mk_rootT]`. Conclude with `congrArg (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)})) (Subtype.ext ((GlobalTheory.RingIface.sigO_coe l g (rootT x n)).trans (h n)) : Per.σO g (rootT x n) = rootT x n * rootT e n)`.
-/
theorem gal_eq_mul (g : GQ l) (x e : Per.Fl l)
    (h : ∀ m, Per.σC g (rootT x m : ℂ_[l]) = (rootT x m : ℂ_[l]) * (rootT e m : ℂ_[l])) :
    Per.σF g x = x * e := by
  refine Perfection.ext fun n => ?_
  refine (GlobalTheory.AdicMaps.coeff_galois l g x n (rootT x n) (coeff_eq_mk_rootT x n)).trans ?_
  change _ = PreTilt.coeff n (x * e)
  rw [map_mul, coeff_eq_mk_rootT, coeff_eq_mk_rootT]
  exact congrArg (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}))
    (Subtype.ext ((GlobalTheory.RingIface.sigO_coe l g (rootT x n)).trans (h n)) :
      Per.σO g (rootT x n) = rootT x n * rootT e n)

/- English proof (translation)
Simplify using `only [map_sub, map_mul, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_quot {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x e v : A) :
    f (x * e * v - 1) = f (x * v - 1) + f (e - 1) + f (x * v - 1) * f (e - 1) := by
  simp only [map_sub, map_mul, map_one]
  ring

/- English proof (translation)
Establish `e1 : Per.σA g (Per.tm x) = Per.tm x * Per.tm e`. Rewrite using `[← map_mul (WittVector.teichmuller l), ← h]`. Conclude with `GlobalTheory.RingIface.sigA_teich l g x`. Rewrite using `[map_sub, map_mul, map_one, (ActLaws.act_laws l).2.2.2.2.2.2.2.1, e1]`.
-/
theorem gal_quot (g : GQ l) (x e : Per.Fl l) (h : Per.σF g x = x * e) (v : ℤ_[l]) :
    Per.σA g (Per.tm x * Per.zA l v - 1) = Per.tm x * Per.tm e * Per.zA l v - 1 := by
  have e1 : Per.σA g (Per.tm x) = Per.tm x * Per.tm e := by
    rw [← map_mul (WittVector.teichmuller l), ← h]
    exact GlobalTheory.RingIface.sigA_teich l g x
  rw [map_sub, map_mul, map_one, (ActLaws.act_laws l).2.2.2.2.2.2.2.1, e1]

section Unit

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

/- English proof (translation)
Take `⟨x, hx⟩` from `exists_tilt μ hs _ h0`. Establish `hu : IsUnit ((l + 1 : ℕ) : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]`. Simplify using the standard rewrite rules. Take `⟨v, hv⟩` from `hu.exists_right_inv`.

Establish `hv' : ((l + 1 : ℕ) : Per.Ainf l) * Per.zA l v = 1`. Use `congrArg (Per.zA l) hv` as an intermediate fact. Rewrite `this` using `[map_mul, map_natCast, map_one]`. Then use the resulting hypothesis. Establish `hx0 : x.untilt = ((l + 1 : ℕ) : Per.OC l)` using `Subtype.ext (by`. Use `hx 0` as an intermediate fact.

Rewrite `this` using `[h0, map_natCast]`. Conclude with `this.trans (SubringClass.coe_natCast _ _).symm)`. Establish `hz : Per.θ l (Per.tm x * Per.zA l v - 1) = 0`. Use `congrArg (Per.θ l) hv'` as an intermediate fact. Rewrite `this` using `[map_mul, map_natCast, map_one]`.

Rewrite using `[map_sub, map_mul, map_one, WittVector.fontaineTheta_teichmuller, hx0, this, sub_self]`. Take `⟨Y, hY⟩` from `GlobalTheory.MemLoc.LogKer.exists_log l C.j C.j_cris _ hz`. Use `⟨Y, fun g d hd => ?_⟩` and prove the remaining obligations. Establish `hμ : ∀ m, μ m ≠ 0` using `fun m h => by`. Use `zeta_pow_iter hs 0 m` as an intermediate fact.

Rewrite `this` using `[zero_add, h0, h, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]`. Conclude with `Nat.cast_ne_zero.2 (Nat.succ_ne_zero l) this.symm`. Establish `hd' : ∀ m, g (μ m) / μ m = C.ζ m ^ (PadicInt.toZModPow m d).val` using `fun m => by`. Rewrite using `[hd, mul_div_cancel_right₀ _ (hμ m)]`. Take `⟨e, he⟩` from `exists_tilt (fun m => C.ζ m ^ (PadicInt.toZModPow m d).val) (fun m => by rw [← hd', ← hd', div_pow, ← map_pow, hs]) 1 (by simp [C.ζ_zero])`.

Establish `he1 : e.untilt = 1` using `Subtype.ext (by`. Use `he 0` as an intermediate fact. Rewrite `this` using `[C.ζ_zero, one_pow, map_one]`. Conclude with `this)`. Establish `hxe : Per.σF g x = x * e` using `gal_eq_mul g x e fun m => by`.

Rewrite using `[hx, he, ← map_mul, mul_comm, ← hd]`. Conclude with `GlobalTheory.RingBasics.σC_coe g _`. Take `⟨y, -, hy, -⟩` from `exists_isLogA l e he1`. Rewrite using `[← log_eq C e d y he hy]`. Apply `crisP_injective l C.j C.j_cris` to reduce the goal to its premises.

Rewrite using `[map_add, CrisUnique.equivariant C.j_cris]`. Use `IsLogP.add ((ThetaD.fontaineTheta_eq_zero l _).1 (by rw [ThetaD.fontaineTheta_algebraMap₂, hz]; rfl)) (LogFun.mu_mem he1) hY (GlobalTheory.CrisIncl.factorial_mul_ev l e _ he1 (LogFun.isLog_map he1 hy C.j_cris)) ?_` and prove the remaining obligations. Establish `h` using `IsLogP.gal hY g`. Rewrite `h` using `[GlobalTheory.RingBasics.awayMap_algebraMap₂, gal_quot g x e hxe v, map_quot]`. Then use the resulting hypothesis.
-/
theorem exists_period_acris (C : Core l) (μ : ℕ → Om l) (hs : ∀ m, μ (m + 1) ^ l = μ m)
    (h0 : μ 0 = ((l + 1 : ℕ) : Om l)) : ∃ Y : Per.Acris l, ∀ (g : GQ l) (d : ℤ_[l]),
      (∀ m, g (μ m) = C.ζ m ^ (PadicInt.toZModPow m d).val * μ m) →
      sigA g Y = Y + algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l d) * C.t := by
  obtain ⟨x, hx⟩ := exists_tilt μ hs _ h0
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hv' : ((l + 1 : ℕ) : Per.Ainf l) * Per.zA l v = 1 := by
    have := congrArg (Per.zA l) hv
    rwa [map_mul, map_natCast, map_one] at this
  have hx0 : x.untilt = ((l + 1 : ℕ) : Per.OC l) := Subtype.ext (by
    have := hx 0
    rw [h0, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  have hz : Per.θ l (Per.tm x * Per.zA l v - 1) = 0 := by
    have := congrArg (Per.θ l) hv'
    rw [map_mul, map_natCast, map_one] at this
    rw [map_sub, map_mul, map_one, WittVector.fontaineTheta_teichmuller, hx0, this, sub_self]
  obtain ⟨Y, hY⟩ := GlobalTheory.MemLoc.LogKer.exists_log l C.j C.j_cris _ hz
  refine ⟨Y, fun g d hd => ?_⟩
  have hμ : ∀ m, μ m ≠ 0 := fun m h => by
    have := zeta_pow_iter hs 0 m
    rw [zero_add, h0, h, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at this
    exact Nat.cast_ne_zero.2 (Nat.succ_ne_zero l) this.symm
  have hd' : ∀ m, g (μ m) / μ m = C.ζ m ^ (PadicInt.toZModPow m d).val := fun m => by
    rw [hd, mul_div_cancel_right₀ _ (hμ m)]
  obtain ⟨e, he⟩ := exists_tilt (fun m => C.ζ m ^ (PadicInt.toZModPow m d).val)
    (fun m => by rw [← hd', ← hd', div_pow, ← map_pow, hs]) 1 (by simp [C.ζ_zero])
  have he1 : e.untilt = 1 := Subtype.ext (by
    have := he 0
    rw [C.ζ_zero, one_pow, map_one] at this
    exact this)
  have hxe : Per.σF g x = x * e := gal_eq_mul g x e fun m => by
    rw [hx, he, ← map_mul, mul_comm, ← hd]
    exact GlobalTheory.RingBasics.σC_coe g _
  obtain ⟨y, -, hy, -⟩ := exists_isLogA l e he1
  rw [← log_eq C e d y he hy]
  apply crisP_injective l C.j C.j_cris
  rw [map_add, CrisUnique.equivariant C.j_cris]
  refine IsLogP.add ((ThetaD.fontaineTheta_eq_zero l _).1 (by rw [ThetaD.fontaineTheta_algebraMap₂, hz]; rfl)) (LogFun.mu_mem he1) hY
    (GlobalTheory.CrisIncl.factorial_mul_ev l e _ he1 (LogFun.isLog_map he1 hy C.j_cris)) ?_
  have h := IsLogP.gal hY g
  rwa [GlobalTheory.RingBasics.awayMap_algebraMap₂, gal_quot g x e hxe v, map_quot] at h

/- English proof (translation)
Take `⟨C, hC⟩` from `FitsEx.exists_fits l P AI T`. Use `choose r hr using fun x : Om l => IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos`. Establish `hs : ∀ m, r^[m + 1] ((l + 1 : ℕ) : Om l) ^ l = r^[m] ((l + 1 : ℕ) : Om l)` using `fun m => by`. Rewrite using `[Function.iterate_succ_apply', hr]`. Use `choose d hd using exists_exponent P (fun m => r^[m] ((l + 1 : ℕ) : Om l)) hs _ (Nat.succ_ne_zero l) rfl`.

Take `⟨Y, hY⟩` from `exists_period_acris C (fun m => r^[m] ((l + 1 : ℕ) : Om l)) hs rfl`. Use `⟨_, d, T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) Y), fun m => ?_, hd, fun g => ?_⟩` and prove the remaining obligations. Use `zeta_pow_iter (ζ := fun m => r^[m] ((l + 1 : ℕ) : Om l)) hs 0 m` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Apply `T.eB.injective` to reduce the goal to its premises.

Rewrite using `[map_sub, T.actB, RingEquiv.apply_symm_apply, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1, hY g (d g) (by rw [hC.ζ]; exact hd g), Algebra.smul_def, map_mul, T.zB, hC.t, map_add, map_mul, add_sub_cancel_left, GlobalTheory.RingIface.zB_alg]`. Both sides reduce to the same expression.
-/
theorem exists_unit_period {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) :
    ∃ (μ : ℕ → Om l) (d : GQ l → ℤ_[l]) (y : P.R.B), (∀ m : ℕ, μ m ^ (l ^ m) = ((l + 1 : ℕ) : Om l)) ∧
      (∀ (g : GQ l) (m : ℕ), g (μ m) = P.ζQ m ^ (PadicInt.toZModPow m (d g)).val * μ m) ∧
      ∀ g : GQ l, P.actQ g y - y = (d g : ℚ_[l]) • P.tB := by
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  choose r hr using fun x : Om l => IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos
  have hs : ∀ m, r^[m + 1] ((l + 1 : ℕ) : Om l) ^ l = r^[m] ((l + 1 : ℕ) : Om l) := fun m => by
    rw [Function.iterate_succ_apply', hr]
  choose d hd using exists_exponent P (fun m => r^[m] ((l + 1 : ℕ) : Om l)) hs _ (Nat.succ_ne_zero l) rfl
  obtain ⟨Y, hY⟩ := exists_period_acris C (fun m => r^[m] ((l + 1 : ℕ) : Om l)) hs rfl
  refine ⟨_, d, T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) Y), fun m => ?_, hd, fun g => ?_⟩
  · have := zeta_pow_iter (ζ := fun m => r^[m] ((l + 1 : ℕ) : Om l)) hs 0 m
    rwa [zero_add] at this
  · apply T.eB.injective
    rw [map_sub, T.actB, RingEquiv.apply_symm_apply, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1,
      hY g (d g) (by rw [hC.ζ]; exact hd g), Algebra.smul_def, map_mul, T.zB, hC.t, map_add, map_mul,
      add_sub_cancel_left, GlobalTheory.RingIface.zB_alg]
    rfl

end Unit

/- English proof (translation)
Take `⟨k, hk⟩` from `(P.PD (botExt l)).invB (P.φB b - (l : ℚ_[l]) • b) fun g => by`. Rewrite using `[P.PD_actB, map_sub, map_smul, ← phiB_actQ, sub_eq_iff_eq_add.1 (h g), map_add, map_smul, localPrime_frobenius_periodT, smul_add, smul_comm]`. Normalize the expressions using the abelian group laws. Take `⟨a, ha⟩` from `IntermediateField.mem_bot.1 k.2.1`. Establish `hka : k = algebraMap ℚ_[l] _ a` using `Subtype.ext ha.symm`.

Rewrite `hk` using `[hka, ← IsScalarTower.algebraMap_apply]`. Establish `hl : (l : ℚ_[l]) - 1 ≠ 0` using `sub_ne_zero.2 (by exact_mod_cast (Fact.out : l.Prime).ne_one)`. Use `⟨b + algebraMap ℚ_[l] _ (a / ((l : ℚ_[l]) - 1)), ?_, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, AlgHom.commutes, smul_add, eq_sub_iff_add_eq.1 hk |>.symm, Algebra.smul_def (l : ℚ_[l]) (algebraMap _ _ _), ← map_mul, add_comm (algebraMap _ _ a), add_assoc, ← map_add]`. Use `congr 2`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, AlgEquiv.commutes, ← h g]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_phi_eq (P : LocPrime l) (b : P.R.B) (c : GQ l → ℚ_[l])
    (h : ∀ g : GQ l, P.actQ g b - b = c g • P.tB) :
    ∃ b' : P.R.B, P.φB b' = (l : ℚ_[l]) • b' ∧ ∀ g : GQ l, P.actQ g b' - b' = c g • P.tB := by
  obtain ⟨k, hk⟩ := (P.PD (botExt l)).invB (P.φB b - (l : ℚ_[l]) • b) fun g => by
    rw [P.PD_actB, map_sub, map_smul, ← phiB_actQ, sub_eq_iff_eq_add.1 (h g), map_add, map_smul, localPrime_frobenius_periodT,
      smul_add, smul_comm]
    abel
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 k.2.1
  have hka : k = algebraMap ℚ_[l] _ a := Subtype.ext ha.symm
  rw [hka, ← IsScalarTower.algebraMap_apply] at hk
  have hl : (l : ℚ_[l]) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (Fact.out : l.Prime).ne_one)
  refine ⟨b + algebraMap ℚ_[l] _ (a / ((l : ℚ_[l]) - 1)), ?_, fun g => ?_⟩
  · rw [map_add, AlgHom.commutes, smul_add, eq_sub_iff_add_eq.1 hk |>.symm, Algebra.smul_def (l : ℚ_[l]) (algebraMap _ _ _),
      ← map_mul, add_comm (algebraMap _ _ a), add_assoc, ← map_add]
    congr 2
    field_simp
    ring
  · rw [map_add, AlgEquiv.commutes, ← h g]; abel

/- English proof (translation)
Take `⟨r, hr⟩` from `(P.PD (botExt l)).fund (b * tInv P) (by rw [P.PD_φ, map_mul, h, smul_mul_assoc, ← mul_smul_comm, smul_phiB_tInv]) (by rwa [P.PD_ι])`. Conclude with `⟨r, by rw [Algebra.smul_def, hr, mul_assoc, tInv_mul, mul_one]⟩`.
-/
theorem eq_smul_t (P : LocPrime l) (b : P.R.B) (h : P.φB b = (l : ℚ_[l]) • b)
    (hf : P.ιB (b * tInv P) ∈ (P.PD (botExt l)).Fil 0) : ∃ r : ℚ_[l], b = r • P.tB := by
  obtain ⟨r, hr⟩ := (P.PD (botExt l)).fund (b * tInv P)
    (by rw [P.PD_φ, map_mul, h, smul_mul_assoc, ← mul_smul_comm, smul_phiB_tInv]) (by rwa [P.PD_ι])
  exact ⟨r, by rw [Algebra.smul_def, hr, mul_assoc, tInv_mul, mul_one]⟩

/- English proof (translation)
The claim follows from `((P.PD (botExt l)).Fil 0).smul_of_tower_mem a hx`.
-/
theorem smul_mem_Fil (P : LocPrime l) (a : ℚ_[l]) {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0) :
    a • x ∈ (P.PD (botExt l)).Fil 0 :=
  ((P.PD (botExt l)).Fil 0).smul_of_tower_mem a hx

/- English proof (translation)
Introduce `l _ P AI T K b₀ h₀`. Take `⟨b₁, h₁⟩` from `exists_full P K b₀ h₀`. Take `⟨b, hφb, hb⟩` from `exists_phi_eq P b₁ _ h₁`. Take `⟨μ, d, y₁, hμ, hd, hy₁⟩` from `exists_unit_period T`. Take `⟨y, hφy, hy⟩` from `exists_phi_eq P y₁ _ hy₁`.

Take `⟨a, ha⟩` from `GlobalTheory.Pst.NoLogTheta.main l P AI T b _ hb`. Take `⟨s, hs⟩` from `GlobalTheory.Pst.NoLogTheta.main l P AI T y _ hy`. Use `nontrivial_B P` as an intermediate fact. Establish `key : ∀ α β : ℚ_[l], α * a + β * s = 0 → α = 0 ∧ β = 0`. Introduce `α β hαβ`.

Take `⟨r, hr⟩` from `eq_smul_t P (α • b + β • y) (by`. Rewrite using `[map_add, map_smul, map_smul, hφb, hφy, smul_add, smul_comm α, smul_comm β]) (by`. Establish `e : (α • b + β • y) * tInv P = α • ((b - algebraMap ℚ_[l] P.R.B a) * tInv P) + β • ((y - algebraMap ℚ_[l] P.R.B s) * tInv P)`. Use `congrArg (algebraMap ℚ_[l] P.R.B) hαβ` as an intermediate fact. Rewrite `this` using `[map_add, map_mul, map_mul, map_zero]`.

Simplify using `only [Algebra.smul_def]`. Take the linear combination `tInv P * this`. Rewrite using `[e, map_add, map_smul, map_smul]`. Conclude with `add_mem (smul_mem_Fil P α ha) (smul_mem_Fil P β hs))`. Use `GlobalTheory.Pst.KummerIndep.kummer_indep l P μ d hμ hd α β r fun g => ?_` and prove the remaining obligations.

Use `smul_left_injective ℚ_[l] (isUnit_tB P).ne_zero ?_` and prove the remaining obligations. Establish `e` using `congrArg (fun x => P.actQ g x - x) hr`. Simplify using `only [map_add, map_smul, localPrime_galoisAction_periodT] at e`. Rewrite `e` using `[sub_eq_iff_eq_add.1 (hb g), sub_eq_iff_eq_add.1 (hy g)]`. Simplify using `only [Algebra.smul_def, map_add, map_mul, map_sub, map_one] at e ⊢`.

Take the linear combination `e`. Take `⟨h1, -⟩` from `key s (-a) (by ring)`. Conclude with `one_ne_zero (key 0 1 (by rw [h1]; ring)).2`.
-/
theorem kummer_not_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (b : P.R.B), ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB := by
  intro l _ P AI T K b₀ h₀
  obtain ⟨b₁, h₁⟩ := exists_full P K b₀ h₀
  obtain ⟨b, hφb, hb⟩ := exists_phi_eq P b₁ _ h₁
  obtain ⟨μ, d, y₁, hμ, hd, hy₁⟩ := exists_unit_period T
  obtain ⟨y, hφy, hy⟩ := exists_phi_eq P y₁ _ hy₁
  obtain ⟨a, ha⟩ := GlobalTheory.Pst.NoLogTheta.main l P AI T b _ hb
  obtain ⟨s, hs⟩ := GlobalTheory.Pst.NoLogTheta.main l P AI T y _ hy
  have := nontrivial_B P
  have key : ∀ α β : ℚ_[l], α * a + β * s = 0 → α = 0 ∧ β = 0 := by
    intro α β hαβ
    obtain ⟨r, hr⟩ := eq_smul_t P (α • b + β • y) (by
      rw [map_add, map_smul, map_smul, hφb, hφy, smul_add, smul_comm α, smul_comm β]) (by
      have e : (α • b + β • y) * tInv P = α • ((b - algebraMap ℚ_[l] P.R.B a) * tInv P) +
          β • ((y - algebraMap ℚ_[l] P.R.B s) * tInv P) := by
        have := congrArg (algebraMap ℚ_[l] P.R.B) hαβ
        rw [map_add, map_mul, map_mul, map_zero] at this
        simp only [Algebra.smul_def]
        linear_combination tInv P * this
      rw [e, map_add, map_smul, map_smul]
      exact add_mem (smul_mem_Fil P α ha) (smul_mem_Fil P β hs))
    refine GlobalTheory.Pst.KummerIndep.kummer_indep l P μ d hμ hd α β r fun g => ?_
    refine smul_left_injective ℚ_[l] (isUnit_tB P).ne_zero ?_
    have e := congrArg (fun x => P.actQ g x - x) hr
    simp only [map_add, map_smul, localPrime_galoisAction_periodT] at e
    rw [sub_eq_iff_eq_add.1 (hb g), sub_eq_iff_eq_add.1 (hy g)] at e
    simp only [Algebra.smul_def, map_add, map_mul, map_sub, map_one] at e ⊢
    linear_combination e
  obtain ⟨h1, -⟩ := key s (-a) (by ring)
  exact one_ne_zero (key 0 1 (by rw [h1]; ring)).2

end GlobalTheory.Pst.NoLog
