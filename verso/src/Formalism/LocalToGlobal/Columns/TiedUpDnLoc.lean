import Formalism.LocalToGlobal.Columns.TiedLv

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt redFn resS)

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨D, hD, hDa⟩` from `levelaf_denom (E := E) a`. Take `⟨p, hp, hp0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`. Use `set DE : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) D with hDE`. Establish `hDE0 : DE ≠ 0`. Rewrite using `[hDE, Ne, FaithfulSMul.algebraMap_eq_zero_iff]`.

Conclude with `hD`. Establish `hI : (Ideal.span {p * DE} : Ideal (𝓞 E)) ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `mul_ne_zero hp0 hDE0`. Take `⟨q, hq⟩` from `Formalism.L2.DIV.cmpS_surj (F := F) _ hI (Ideal.Quotient.mk _ (Formalism.L2.DIV.lc_eps E v))`.

Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Establish `hq' : Ideal.Quotient.mk (Formalism.L2.DIV.idS F (Ideal.span {p * DE})) (Formalism.L2.DIV.oToS F E t) = Ideal.Quotient.mk _ (Formalism.L2.DIV.lc_eps E v)` using `hq`. Establish `hd` using `Ideal.Quotient.eq.1 hq'`. Unfold `Formalism.L2.DIV.idS at hd`. Rewrite `hd` using `[Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']`.

Take `⟨y, hy⟩` from `hd`. Establish `ht : Formalism.L2.DIV.oToS F E t = Formalism.L2.DIV.lc_eps E v + y * Formalism.L2.DIV.oToS F E p * Formalism.L2.DIV.oToS F E DE`. Rewrite using `[mul_assoc, ← map_mul, hy]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨t, ?_, ?_⟩` and prove the remaining obligations.

Introduce `htP`. Establish `h1` using `congrArg (resS F P) ht`. Rewrite `h1` using `[map_add, map_mul, map_mul, Formalism.L2.DIV.lc_res_eps P v hov, Formalism.L2.DIV.resS_oToS, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 htP, Ideal.Quotient.eq_zero_iff_mem.2 hp, mul_zero, zero_mul, add_zero]`. Conclude with `zero_ne_one h1`. Establish `hC : ((Formalism.L2.DIV.oToS F E DE : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = levelafC E D`.

Rewrite using `[Formalism.L2.DIV.levelafC_eq_incl, ← iA_coe, hDE, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[iA_coe, ht]`. Establish `e : ((Formalism.L2.DIV.lc_eps E v + y * Formalism.L2.DIV.oToS F E p * Formalism.L2.DIV.oToS F E DE : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * a = afsplitIE v (prV (E` using `E) v a) + ((y * Formalism.L2.DIV.oToS F E p : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * (levelafC E D * a) := by`. Rewrite using `[afsplit_decomp, ← hC, Subring.coe_add, Subring.coe_mul, add_mul, mul_assoc]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `add_mem (afsplit_IE_int v _ h) (mul_mem (y * Formalism.L2.DIV.oToS F E p).2 hDa)`.
-/
theorem updn_den {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P) (a : E ⊗[F] Formalism.L2.Herm.Af F)
    (h : prV (E := E) v a ∈ Formalism.BasicNotions.intV E v) :
    ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ iA F E (algebraMap (𝓞 E) E t) * a ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨D, hD, hDa⟩ := levelaf_denom (E := E) a
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  set DE : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) D with hDE
  have hDE0 : DE ≠ 0 := by
    rw [hDE, Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact hD
  have hI : (Ideal.span {p * DE} : Ideal (𝓞 E)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hp0 hDE0
  obtain ⟨q, hq⟩ := Formalism.L2.DIV.cmpS_surj (F := F) _ hI (Ideal.Quotient.mk _ (Formalism.L2.DIV.lc_eps E v))
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hq' : Ideal.Quotient.mk (Formalism.L2.DIV.idS F (Ideal.span {p * DE})) (Formalism.L2.DIV.oToS F E t) =
      Ideal.Quotient.mk _ (Formalism.L2.DIV.lc_eps E v) := hq
  have hd := Ideal.Quotient.eq.1 hq'
  unfold Formalism.L2.DIV.idS at hd
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hd
  obtain ⟨y, hy⟩ := hd
  have ht : Formalism.L2.DIV.oToS F E t = Formalism.L2.DIV.lc_eps E v + y * Formalism.L2.DIV.oToS F E p * Formalism.L2.DIV.oToS F E DE := by
    rw [mul_assoc, ← map_mul, hy]; ring
  refine ⟨t, ?_, ?_⟩
  · intro htP
    have h1 := congrArg (resS F P) ht
    rw [map_add, map_mul, map_mul, Formalism.L2.DIV.lc_res_eps P v hov, Formalism.L2.DIV.resS_oToS, Formalism.L2.DIV.resS_oToS,
      Ideal.Quotient.eq_zero_iff_mem.2 htP, Ideal.Quotient.eq_zero_iff_mem.2 hp, mul_zero, zero_mul, add_zero] at h1
    exact zero_ne_one h1
  · have hC : ((Formalism.L2.DIV.oToS F E DE : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = levelafC E D := by
      rw [Formalism.L2.DIV.levelafC_eq_incl, ← iA_coe, hDE, ← IsScalarTower.algebraMap_apply]
    rw [iA_coe, ht]
    have e : ((Formalism.L2.DIV.lc_eps E v + y * Formalism.L2.DIV.oToS F E p * Formalism.L2.DIV.oToS F E DE : Formalism.L2.Herm.intAf F E) :
        E ⊗[F] Formalism.L2.Herm.Af F) * a = afsplitIE v (prV (E := E) v a) +
          ((y * Formalism.L2.DIV.oToS F E p : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * (levelafC E D * a) := by
      rw [afsplit_decomp, ← hC, Subring.coe_add, Subring.coe_mul, add_mul, mul_assoc]
      rfl
    rw [e]
    exact add_mem (afsplit_IE_int v _ h) (mul_mem (y * Formalism.L2.DIV.oToS F E p).2 hDa)

variable {n : ℕ}

/- English proof (translation)
Establish `h' : bc (prV (E` using `E) v) x⁻¹ = bc (prV (E := E) v) x'⁻¹ := by rw [map_inv, map_inv, h]`. Unfold `pullV`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul]`. Use `congr 1`. Conclude with `congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) => (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) h'`.
-/
theorem updn_prV_pullV {v : HeightOneSpectrum (𝓞 F)} {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') (z : Fin n → E) (i : Fin n) :
    prV (E := E) v (pullV x z i) = prV (E := E) v (pullV x' z i) := by
  have h' : bc (prV (E := E) v) x⁻¹ = bc (prV (E := E) v) x'⁻¹ := by rw [map_inv, map_inv, h]
  unfold pullV
  simp only [Matrix.mulVec, dotProduct]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul]
  congr 1
  exact congrArg (fun g : GL (Fin n) (E ⊗[F] v.adicCompletion F) =>
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) h'

variable [StarRing E]

/- English proof (translation)
Introduce `z hz`. Take `⟨s, hs, hsz⟩` from `(mem_locP P _ z).1 hz`. Establish `h1 : ∀ i, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ iA F E (algebraMap (𝓞 E) E t) * pullV x' (s • z) i ∈ Formalism.L2.Herm.intAf F E` using `fun i => updn_den hov _ (by`. Rewrite using `[← updn_prV_pullV h]`. Conclude with `afsplit_prV_int v _ ((mem_globLat x _).1 hsz i))`.

Use `choose t ht hti using h1`. Establish `hT : (∏ i, t i) ∉ P.asIdeal`. Introduce `hm`. Take `⟨i, -, hi⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm`. Conclude with `ht i hi`.

Use `(mem_locP P _ z).2 ⟨(∏ i, t i) * s, fun hm => (P.isPrime.mem_or_mem hm).elim hT hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, mem_globLat]`. Introduce `i`. Rewrite using `[pullV_osmul, ← Finset.prod_erase_mul Finset.univ t (Finset.mem_univ i), map_mul, map_mul, mul_assoc]`. Conclude with `mul_mem (iA_mem _) (hti i)`.
-/
theorem localized_globalLattice_le {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) ≤ localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) := by
  classical
  intro z hz
  obtain ⟨s, hs, hsz⟩ := (mem_locP P _ z).1 hz
  have h1 : ∀ i, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧
      iA F E (algebraMap (𝓞 E) E t) * pullV x' (s • z) i ∈ Formalism.L2.Herm.intAf F E := fun i =>
    updn_den hov _ (by
      rw [← updn_prV_pullV h]
      exact afsplit_prV_int v _ ((mem_globLat x _).1 hsz i))
  choose t ht hti using h1
  have hT : (∏ i, t i) ∉ P.asIdeal := by
    intro hm
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
    exact ht i hi
  refine (mem_locP P _ z).2 ⟨(∏ i, t i) * s, fun hm => (P.isPrime.mem_or_mem hm).elim hT hs, ?_⟩
  rw [mul_smul, mem_globLat]
  intro i
  rw [pullV_osmul, ← Finset.prod_erase_mul Finset.univ t (Finset.mem_univ i), map_mul, map_mul, mul_assoc]
  exact mul_mem (iA_mem _) (hti i)

/- English proof (translation)
The claim follows from `le_antisymm (localized_globalLattice_le hov h) (localized_globalLattice_le hov h.symm)`.
-/
theorem updn_mem_loc {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) = localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) :=
  le_antisymm (localized_globalLattice_le hov h) (localized_globalLattice_le hov h.symm)

/- English proof (translation)
Establish `hz' : z ∈ localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n))` using `localized_globalLattice_le hov h hz`. Take `⟨s, hs, hsz⟩` from `pullV_den hz`. Take `⟨s', hs', hsz'⟩` from `pullV_den hz'`. Establish `hss : s * s' ∉ P.asIdeal` using `fun hm => (P.isPrime.mem_or_mem hm).elim hs hs'`. Establish `m1 : iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x z i ∈ Formalism.L2.Herm.intAf F E`.

Rewrite using `[mul_comm s s', map_mul, map_mul, mul_assoc]`. Conclude with `mul_mem (iA_mem _) (hsz i)`. Establish `m2 : iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x' z i ∈ Formalism.L2.Herm.intAf F E`. Rewrite using `[map_mul, map_mul, mul_assoc]`. Conclude with `mul_mem (iA_mem _) (hsz' i)`.

Apply `mul_left_cancel₀ (mk_ne_zero hss)` to reduce the goal to its premises. Rewrite using `[redA_spec P hss m1, redA_spec P hss m2, ← sub_eq_zero, ← map_sub]`. Use `Formalism.L2.DIV.resS_eq_zero_of_prV P v hov _ ?_` and prove the remaining obligations. Use `show prV (E := E) v (iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x z i - iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x' z i) = 0`. Rewrite using `[map_sub, map_mul (prV (E := E) v), map_mul (prV (E := E) v), updn_prV_pullV h, sub_self]`.
-/
theorem updn_red_loc {v : HeightOneSpectrum (𝓞 F)} {P : Pl E} (hov : IsOver v P)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') {z : Fin n → E}
    (hz : z ∈ localization₂ P.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))) (i : Fin n) :
    redA P (pullV x z i) = redA P (pullV x' z i) := by
  have hz' : z ∈ localization₂ P.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) := localized_globalLattice_le hov h hz
  obtain ⟨s, hs, hsz⟩ := pullV_den hz
  obtain ⟨s', hs', hsz'⟩ := pullV_den hz'
  have hss : s * s' ∉ P.asIdeal := fun hm => (P.isPrime.mem_or_mem hm).elim hs hs'
  have m1 : iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x z i ∈ Formalism.L2.Herm.intAf F E := by
    rw [mul_comm s s', map_mul, map_mul, mul_assoc]
    exact mul_mem (iA_mem _) (hsz i)
  have m2 : iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x' z i ∈ Formalism.L2.Herm.intAf F E := by
    rw [map_mul, map_mul, mul_assoc]
    exact mul_mem (iA_mem _) (hsz' i)
  apply mul_left_cancel₀ (mk_ne_zero hss)
  rw [redA_spec P hss m1, redA_spec P hss m2, ← sub_eq_zero, ← map_sub]
  refine Formalism.L2.DIV.resS_eq_zero_of_prV P v hov _ ?_
  show prV (E := E) v (iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x z i -
    iA F E (algebraMap (𝓞 E) E (s * s')) * pullV x' z i) = 0
  rw [map_sub, map_mul (prV (E := E) v), map_mul (prV (E := E) v), updn_prV_pullV h, sub_self]

variable [NeZero n] (ST SG : Finset (Pl E))

/- English proof (translation)
Use function extensionality and compare the values at `z`. Use `show (open Classical in if z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) then redA P.1 (pullV x z (lastIdx n)) else 0) = (open Classical in if z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) then redA P.1 (pullV x' z (lastIdx n)) e …`. Rewrite using `[← updn_mem_loc hov h]`. Distinguish the cases in `hz : z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))`. Rewrite using `[if_pos hz, if_pos hz, updn_red_loc hov h hz]`.

Rewrite using `[if_neg hz, if_neg hz]`.
-/
theorem updn_f_loc {v : HeightOneSpectrum (𝓞 F)} (P : ST) (hov : IsOver v P.1)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    (decoRaw ST SG x).f P = (decoRaw ST SG x').f P := by
  funext z
  show (open Classical in if z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
      then redA P.1 (pullV x z (lastIdx n)) else 0) =
    (open Classical in if z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n))
      then redA P.1 (pullV x' z (lastIdx n)) else 0)
  rw [← updn_mem_loc hov h]
  by_cases hz : z ∈ localization₂ P.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
  · rw [if_pos hz, if_pos hz, updn_red_loc hov h hz]
  · rw [if_neg hz, if_neg hz]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Use `show (open Classical in if z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n)) then fun i => redA w.1 (pullV x z i) else 0) = (open Classical in if z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n)) then fun i => redA w.1 (pullV x' z i) els …`. Rewrite using `[← updn_mem_loc hov h]`. Distinguish the cases in `hz : z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))`. Rewrite using `[if_pos hz, if_pos hz]`.

Use function extensionality and compare the values at `i`. Conclude with `updn_red_loc hov h hz i`. Rewrite using `[if_neg hz, if_neg hz]`.
-/
theorem updn_be_loc {v : HeightOneSpectrum (𝓞 F)} (w : SG) (hov : IsOver v w.1)
    {x x' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') :
    (decoRaw ST SG x).be w = (decoRaw ST SG x').be w := by
  funext z
  show (open Classical in if z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
      then fun i => redA w.1 (pullV x z i) else 0) =
    (open Classical in if z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x' (stdLat E n))
      then fun i => redA w.1 (pullV x' z i) else 0)
  rw [← updn_mem_loc hov h]
  by_cases hz : z ∈ localization₂ w.1.asIdeal (Formalism.UG.CS.globLat x (stdLat E n))
  · rw [if_pos hz, if_pos hz]
    funext i
    exact updn_red_loc hov h hz i
  · rw [if_neg hz, if_neg hz]

structure Deco.SameOff (v : HeightOneSpectrum (𝓞 F)) (d d' : Deco E n ST SG) : Prop where
  N : ∀ Q : Pl E, ¬ IsOver v Q → localization₂ Q.asIdeal d.N = localization₂ Q.asIdeal d'.N
  f : ∀ Q : ST, ¬ IsOver v Q.1 → d.f Q = d'.f Q
  be : ∀ w : SG, ¬ IsOver v w.1 → d.be w = d'.be w

/- English proof (translation)
Establish `hv : bc (prV (E` using `E) v) (y * rll_put n v (bc (prV (E := E) v) (y⁻¹ * x))) = bc (prV (E := E) v) x := by`. Rewrite using `[map_mul, rll_put_self, ← map_mul, mul_inv_cancel_left]`. Establish `hw : ∀ Q : Pl E, ¬ IsOver v Q → bc (prV (E` using `E) (Formalism.L2.DIV.underPl F Q)) (y * rll_put n v (bc (prV (E := E) v) (y⁻¹ * x))) = bc (prV (E := E) (Formalism.L2.DIV.underPl F Q)) y := by`. Introduce `Q hQ`. Establish `hne : Formalism.L2.DIV.underPl F Q ≠ v`.

Introduce and unpack `rfl`. Conclude with `hQ rfl`. Rewrite using `[map_mul, rll_put_ne n v _ hne, mul_one]`. Use `ext1`. Use `Formalism.L2.DIV.eq_of_forall_localized_eq fun Q => ?_` and prove the remaining obligations.

Distinguish the cases in `hQ : IsOver v Q`. Conclude with `updn_mem_loc hQ hv`. Conclude with `(updn_mem_loc (v := Formalism.L2.DIV.underPl F Q) rfl (hw Q hQ)).trans (h.N Q hQ)`. Use function extensionality and compare the values at `Q`. Distinguish the cases in `hQ : IsOver v Q.1`.

Conclude with `updn_f_loc ST SG Q hQ hv`. Conclude with `(updn_f_loc ST SG (v := Formalism.L2.DIV.underPl F Q.1) Q rfl (hw Q.1 hQ)).trans (h.f Q hQ)`. Use function extensionality and compare the values at `w`. Distinguish the cases in `hQ : IsOver v w.1`. Conclude with `updn_be_loc ST SG w hQ hv`.

Conclude with `(updn_be_loc ST SG (v := Formalism.L2.DIV.underPl F w.1) w rfl (hw w.1 hQ)).trans (h.be w hQ)`.
-/
theorem updn_decoRaw_eq (v : HeightOneSpectrum (𝓞 F)) (x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h : Deco.SameOff ST SG v (decoRaw ST SG y) (decoRaw ST SG x)) :
    decoRaw ST SG (y * rll_put n v (bc (prV (E := E) v) (y⁻¹ * x))) = decoRaw ST SG x := by
  have hv : bc (prV (E := E) v) (y * rll_put n v (bc (prV (E := E) v) (y⁻¹ * x))) = bc (prV (E := E) v) x := by
    rw [map_mul, rll_put_self, ← map_mul, mul_inv_cancel_left]
  have hw : ∀ Q : Pl E, ¬ IsOver v Q →
      bc (prV (E := E) (Formalism.L2.DIV.underPl F Q)) (y * rll_put n v (bc (prV (E := E) v) (y⁻¹ * x))) =
        bc (prV (E := E) (Formalism.L2.DIV.underPl F Q)) y := by
    intro Q hQ
    have hne : Formalism.L2.DIV.underPl F Q ≠ v := by
      rintro rfl; exact hQ rfl
    rw [map_mul, rll_put_ne n v _ hne, mul_one]
  ext1
  · refine Formalism.L2.DIV.eq_of_forall_localized_eq fun Q => ?_
    by_cases hQ : IsOver v Q
    · exact updn_mem_loc hQ hv
    · exact (updn_mem_loc (v := Formalism.L2.DIV.underPl F Q) rfl (hw Q hQ)).trans (h.N Q hQ)
  · funext Q
    by_cases hQ : IsOver v Q.1
    · exact updn_f_loc ST SG Q hQ hv
    · exact (updn_f_loc ST SG (v := Formalism.L2.DIV.underPl F Q.1) Q rfl (hw Q.1 hQ)).trans (h.f Q hQ)
  · funext w
    by_cases hQ : IsOver v w.1
    · exact updn_be_loc ST SG w hQ hv
    · exact (updn_be_loc ST SG (v := Formalism.L2.DIV.underPl F w.1) w rfl (hw w.1 hQ)).trans (h.be w hQ)

/- English proof (translation)
The claim follows from `h.N f Q hQ := by funext z show (c Q).1 * d.f Q z = (c Q).1 * d'.f Q z rw [h.f Q hQ] be := h.be`.
-/
theorem Deco.SameOff.dia {v : HeightOneSpectrum (𝓞 F)} {d d' : Deco E n ST SG} (h : Deco.SameOff ST SG v d d')
    (c : DiaG E ST) : Deco.SameOff ST SG v (d.dia c) (d'.dia c) where
  N := h.N
  f Q hQ := by
    funext z
    show (c Q).1 * d.f Q z = (c Q).1 * d'.f Q z
    rw [h.f Q hQ]
  be := h.be

end Loc

section Move

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

/- English proof (translation)
Use `set y := ptOfD hc n ST SG c₀ d with hy`. Use `set x := ptOfD hc n ST SG c₀ d₁ with hx`. Establish `hdy : decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d.dia c₀⁻¹` using `decoOf_ptOf hc n ST SG hS _`. Establish `hdx : decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d₁.dia c₀⁻¹` using `decoOf_ptOf hc n ST SG hS _`. Establish `hry : decoRaw ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d.1.dia c₀⁻¹`.

Rewrite using `[← rlc_decoOf_val hc n ST SG y.2, hdy]`. Both sides reduce to the same expression. Establish `hrx : decoRaw ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d₁.1.dia c₀⁻¹`. Rewrite using `[← rlc_decoOf_val hc n ST SG x.2, hdx]`. Both sides reduce to the same expression.

Set `η : UAd hc n` to `⟨rll_put n v (bc (prV (E := E) v) ((y⁻¹ * x : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))), rll_put_mem_UAd hc n v (afsplit_bc_mem hc.sig 1 v _ (y⁻¹ * x).2)⟩`. Establish `key : decoOf ST SG ((y * η : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = g₀ • decoOf ST SG (ptOfD hc n ST SG c₀ d' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))`. Establish `h1 : decoOf ST SG ((y * η : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d₁.dia c₀⁻¹`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[rlc_decoOf_val hc n ST SG (y * η).2]`.

Use `Eq.trans ?_ hrx` and prove the remaining obligations. Conclude with `updn_decoRaw_eq ST SG v _ _ (by rw [hry, hrx]; exact h.dia ST SG c₀⁻¹)`. Rewrite using `[h1]`. Unfold `ptOfD`. Rewrite using `[decoOf_ptOf hc n ST SG hS, ← hg₀]`.

Conclude with `rla_dia_smulH n ST SG H c₀⁻¹ g₀ d'`. Take `⟨γ, κ, hγ, hκ, e⟩` from `rlc_rel_of_orbit hc n ST SG H g₀ key`. Use `⟨γ, η, κ, hγ, hκ, fun v' hv' => rll_put_ne n v v' hv' _, ?_⟩` and prove the remaining obligations. Rewrite using `[← Subgroup.coe_mul, e, inv_mul_cancel_right]`.
-/
theorem updn_move (hS : DecoPtSurj hc n ST SG) (c₀ : DiaG E ST) (v : HeightOneSpectrum (𝓞 F)) (d d₁ d' : DecoSet E n ST SG)
    (h : Deco.SameOff ST SG v d.1 d₁.1) (g₀ : UF E n × H) (hg₀ : g₀ • d' = d₁) :
    ∃ (γ : URat hc n) (η : UAd hc n) (κ : levU hc n ST SG H), ratHom hc n γ = g₀.1 ∧ levRed hc n ST SG H κ = g₀.2 ∧
      (∀ v', v' ≠ v → bc (prV (E := E) v') (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
      bc (iA F E) (γ : GL (Fin n) E) * (ptOfD hc n ST SG c₀ d' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (ptOfD hc n ST SG c₀ d : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * η * κ := by
  set y := ptOfD hc n ST SG c₀ d with hy
  set x := ptOfD hc n ST SG c₀ d₁ with hx
  have hdy : decoOf ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d.dia c₀⁻¹ := decoOf_ptOf hc n ST SG hS _
  have hdx : decoOf ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d₁.dia c₀⁻¹ := decoOf_ptOf hc n ST SG hS _
  have hry : decoRaw ST SG (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d.1.dia c₀⁻¹ := by
    rw [← rlc_decoOf_val hc n ST SG y.2, hdy]; rfl
  have hrx : decoRaw ST SG (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d₁.1.dia c₀⁻¹ := by
    rw [← rlc_decoOf_val hc n ST SG x.2, hdx]; rfl
  let η : UAd hc n := ⟨rll_put n v (bc (prV (E := E) v) ((y⁻¹ * x : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))),
    rll_put_mem_UAd hc n v (afsplit_bc_mem hc.sig 1 v _ (y⁻¹ * x).2)⟩
  have key : decoOf ST SG ((y * η : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      g₀ • decoOf ST SG (ptOfD hc n ST SG c₀ d' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have h1 : decoOf ST SG ((y * η : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = d₁.dia c₀⁻¹ := by
      apply Subtype.ext
      rw [rlc_decoOf_val hc n ST SG (y * η).2]
      refine Eq.trans ?_ hrx
      exact updn_decoRaw_eq ST SG v _ _ (by rw [hry, hrx]; exact h.dia ST SG c₀⁻¹)
    rw [h1]
    unfold ptOfD
    rw [decoOf_ptOf hc n ST SG hS, ← hg₀]
    exact rla_dia_smulH n ST SG H c₀⁻¹ g₀ d'
  obtain ⟨γ, κ, hγ, hκ, e⟩ := rlc_rel_of_orbit hc n ST SG H g₀ key
  refine ⟨γ, η, κ, hγ, hκ, fun v' hv' => rll_put_ne n v v' hv' _, ?_⟩
  rw [← Subgroup.coe_mul, e, inv_mul_cancel_right]

end Move

end Formalism.L2.Col
