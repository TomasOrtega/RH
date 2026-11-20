import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionRegularAndTorsionBoundedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureAdicCompletionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomOfDenseDeltaCommuteLocusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsAdicCompletionMapOfFgStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingHomExtendIsAdicCompletionMapStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfIsAdicCompletionMapStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismLocalizationSpanNonZeroDivisorBoundedTorsioStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submonoid.closure_induction with`. Consider the case `mem x h`. Take `⟨m, rfl⟩` from `h`. Conclude with `Submonoid.subset_closure ⟨m + 1, by simp only [Function.iterate_succ_apply']⟩`.

Consider the case `one => rw [map_one]`. Conclude with `Submonoid.one_mem _`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `Submonoid.mul_mem _ hx hy`.
-/
theorem locAway_φ_mem {l : ℕ} {A : Type} [CommRing A] (D : Delta l A) (f : A) :
    ∀ x ∈ Submonoid.closure (Set.range fun m : ℕ => D.φ^[m] f),
      D.φ x ∈ Submonoid.closure (Set.range fun m : ℕ => D.φ^[m] f) := by
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    exact Submonoid.subset_closure ⟨m + 1, by simp only [Function.iterate_succ_apply']⟩
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Submonoid.mul_mem _ hx hy

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq]`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `hl0 : ((l : A ⧸ Ideal.span {(l : A)})) = 0`.

Rewrite using `[← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : A)})), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite using `[Function.iterate_succ_apply', D.φ_eq, map_add, map_mul, map_pow, ih, map_natCast, hl0, zero_mul, add_zero, map_pow, map_pow, ← pow_mul, pow_succ]`.
-/
theorem locAway_iterate_sub_mem {l : ℕ} {A : Type} [CommRing A] (D : Delta l A) (f : A) (m : ℕ) :
    D.φ^[m] f - f ^ (l ^ m) ∈ Ideal.span {(l : A)} := by
  rw [← Ideal.Quotient.eq]
  induction m with
  | zero => simp
  | succ m ih =>
    have hl0 : ((l : A ⧸ Ideal.span {(l : A)})) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : A)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    rw [Function.iterate_succ_apply', D.φ_eq, map_add, map_mul, map_pow, ih, map_natCast, hl0, zero_mul,
      add_zero, map_pow, map_pow, ← pow_mul, pow_succ]

/- English proof (translation)
Introduce `s hs`. Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem x h`. Take `⟨m, rfl⟩` from `h`. Establish `h1 : f ^ (l ^ m) - D.φ^[m] f ∈ J`.

Rewrite using `[← neg_sub, neg_mem_iff]`. Conclude with `(Ideal.span_le.2 (Set.singleton_subset_iff.2 hl)) (locAway_iterate_sub_mem D f m)`. Take `⟨t, ht⟩` from `sub_dvd_pow_sub_pow (f ^ (l ^ m)) (f ^ (l ^ m) - D.φ^[m] f) n`. Use `⟨l ^ m * n, t, ?_⟩` and prove the remaining obligations. Establish `e : f ^ (l ^ m * n) - D.φ^[m] f * t = (f ^ (l ^ m) - D.φ^[m] f) ^ n`.

Rewrite using `[pow_mul]`. Establish `e2 : f ^ l ^ m - (f ^ l ^ m - D.φ^[m] f) = D.φ^[m] f` using `by ring`. Rewrite `ht` using `[e2]`. Take the linear combination `ht`. Rewrite using `[e]`.

Conclude with `Ideal.pow_mem_pow h1 n`. Consider the case `one => exact ⟨0, 1, by simp⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨k1, t1, h1⟩` from `hx`. Take `⟨k2, t2, h2⟩` from `hy`.

Use `⟨k1 + k2, t1 * t2, ?_⟩` and prove the remaining obligations. Establish `e : f ^ (k1 + k2) - x * y * (t1 * t2) = f ^ k1 * (f ^ k2 - y * t2) + y * t2 * (f ^ k1 - x * t1)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h1)`.
-/
theorem locAway_dvd_mod {l : ℕ} {A : Type} [CommRing A] (D : Delta l A) (f : A) (J : Ideal A)
    (hl : (l : A) ∈ J) (n : ℕ) :
    ∀ s ∈ Submonoid.closure (Set.range fun m : ℕ => D.φ^[m] f), ∃ (k : ℕ) (t : A), f ^ k - s * t ∈ J ^ n := by
  intro s hs
  induction hs using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    have h1 : f ^ (l ^ m) - D.φ^[m] f ∈ J := by
      rw [← neg_sub, neg_mem_iff]
      exact (Ideal.span_le.2 (Set.singleton_subset_iff.2 hl)) (locAway_iterate_sub_mem D f m)
    obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow (f ^ (l ^ m)) (f ^ (l ^ m) - D.φ^[m] f) n
    refine ⟨l ^ m * n, t, ?_⟩
    have e : f ^ (l ^ m * n) - D.φ^[m] f * t = (f ^ (l ^ m) - D.φ^[m] f) ^ n := by
      rw [pow_mul]
      have e2 : f ^ l ^ m - (f ^ l ^ m - D.φ^[m] f) = D.φ^[m] f := by ring
      rw [e2] at ht
      linear_combination ht
    rw [e]; exact Ideal.pow_mem_pow h1 n
  | one => exact ⟨0, 1, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k1, t1, h1⟩ := hx
    obtain ⟨k2, t2, h2⟩ := hy
    refine ⟨k1 + k2, t1 * t2, ?_⟩
    have e : f ^ (k1 + k2) - x * y * (t1 * t2) = f ^ k1 * (f ^ k2 - y * t2) + y * t2 * (f ^ k1 - x * t1) := by
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h1)

/- English proof (translation)
Introduce `s hs`. Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem x h`. Take `⟨m, rfl⟩` from `h`. Proceed by induction on `m with`.

Consider the case `zero => simpa using hu`. Consider the case `succ m ih => show IsUnit (g.f (B.D.φ^[m + 1] f))`. Express the relevant statement in the definitionally equal form `IsUnit (g.f (B.D.φ^[m] f)) at ih`. Rewrite using `[Function.iterate_succ_apply', g.f_φ]`. Conclude with `ih.map C.D.φ`.

Consider the case `one => rw [map_one]`. Conclude with `isUnit_one`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `hx.mul hy`.
-/
theorem locAway_units {l : ℕ} {R : Type} [CommRing R] {B C : Obj l R} (g : Hom B C) (f : B.A)
    (hu : IsUnit (g.f f)) :
    ∀ s ∈ Submonoid.closure (Set.range fun m : ℕ => B.D.φ^[m] f), IsUnit (g.f s) := by
  intro s hs
  induction hs using Submonoid.closure_induction with
  | mem x h =>
    obtain ⟨m, rfl⟩ := h
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      show IsUnit (g.f (B.D.φ^[m + 1] f))
      change IsUnit (g.f (B.D.φ^[m] f)) at ih
      rw [Function.iterate_succ_apply', g.f_φ]
      exact ih.map C.D.φ
  | one => rw [map_one]; exact isUnit_one
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

end GlobalTheory.BSP

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l _ R _ B f d hg`. Use `set M := Submonoid.closure (Set.range fun m : ℕ => B.D.φ^[m] f) with hM`. Establish `hfM : f ∈ M` using `Submonoid.subset_closure ⟨0, rfl⟩`. Take `⟨DL, hDL⟩` from `GlobalTheory.T.exists_deltaRingStructure_localization l B.A B.D M (locAway_φ_mem B.D f)`. Take `⟨hIL, hdnz, N, hN⟩` from `GlobalTheory.T.prismLocalization_span_nonZeroDivisor_bounded_torsion l R B f d hg M hfM`.

Use `set J : Ideal (Localization M) := Ideal.span {(l : Localization M)} ⊔ Ideal.span {algebraMap B.A (Localization M) d} with hJdef`. Establish `hJ : (JJ B).map (algebraMap B.A (Localization M)) = J`. Rewrite using `[JJ, Ideal.map_sup, hIL, Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `hJfg : J.FG` using `Submodule.FG.sup (Submodule.fg_span_singleton _) (Submodule.fg_span_singleton _)`. Take `⟨Q, _, i, hi⟩` from `GlobalTheory.T.exists_isAdicCompletionMap_of_fg _ J hJfg`.

Establish `hlJ : (l : Localization M) ∈ J` using `Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)`. Take `⟨DQ, hDQ⟩` from `GlobalTheory.T.exists_deltaRingStructure_adicCompletion l _ Q i J hi hlJ DL`. Take `⟨hqnz, hqN⟩` from `GlobalTheory.T.adic_completion_regular_and_torsion_bounded l _ Q i (algebraMap B.A (Localization M) d) N hdnz hN hi`. Use `set g : B.A →+* Q := i.comp (algebraMap B.A (Localization M)) with hgdef`. Establish `hgδ : ∀ x, g (B.D.δ x) = DQ.δ (g x)` using `fun x => by`.

Simplify using `only [hgdef, RingHom.comp_apply]`. Rewrite using `[hDL x, hDQ]`. Establish `hIg : B.I.map g = Ideal.span {g d}`. Rewrite using `[hgdef, ← Ideal.map_map, hIL, Ideal.map_span, Set.image_singleton]`. Both sides reduce to the same expression.

Establish `hIle : B.I ≤ (Ideal.span {g d}).comap g` using `Ideal.map_le_iff_le_comap.1 hIg.le`. Establish `hJi : J.map i = Ideal.span {(l : Q)} ⊔ Ideal.span {g d}`. Rewrite using `[hJdef, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]`. Both sides reduce to the same expression. Establish `hcomp : IsAdicComplete (Ideal.span {(l : Q)} ⊔ Ideal.span {g d}) Q`.

Use `hi.complete` as an intermediate fact. Rewrite `this` using `[hJi]`. Then use the resulting hypothesis. Establish `hgφ : g.comp B.D.φ = DQ.φ.comp g` using `RingHom.ext fun x => Delta.map_φ_of_map_δ B.D DQ g hgδ x`. Establish `hlmem : (l : Q) ∈ Ideal.span {g d} ⊔ (Ideal.span {g d}).map DQ.φ`. Establish `h` using `Ideal.mem_map_of_mem g B.l_mem`.

Establish `hgm : (B.I.map B.D.φ).map g = (B.I.map g).map DQ.φ`. Rewrite using `[Ideal.map_map, Ideal.map_map, hgφ]`. Rewrite `h` using `[map_natCast, Ideal.map_sup, hgm, hIg]`. Then use the resulting hypothesis. Establish `hbdd : ∃ n : ℕ, ∀ x : Q ⧸ Ideal.span {g d}, (∃ m : ℕ, (l : Q ⧸ Ideal.span {g d}) ^ m * x = 0) → (l : Q ⧸ Ideal.span {g d}) ^ n * x = 0`. Use `⟨N, fun x ⟨m, hm⟩ => ?_⟩` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite `hm`, the goal using `[← map_natCast (Ideal.Quotient.mk _), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hqN y m hm`. Set `Qo : Obj l R` to `{ A := Q D := DQ I := Ideal.span {g d} inv := invertible_span_singleton hqnz complete := hcomp l_mem := hlmem bdd := hbdd str := (Ideal.quotientMap (Ideal.span {g d}) g hIle).comp B.str }`. Set `inl : Hom B Qo` to `{ f := g f_δ := hgδ f_I := fun x hx => hIle hx f_str := fun r x h => by show _ = Ideal.quotientMap (Ideal.span {g d}) g hIle (B.str r)`.

Rewrite using `[← h, Ideal.quotientMap_mk] }`. Establish `hlu : ∀ s : M, IsUnit (g s)` using `fun s => (IsLocalization.map_units (Localization M) s).map i`. Establish `hJn : ∀ n : ℕ, ((JJ B) ^ n).map g = (J ^ n).map i` using `fun n => by`. Rewrite using `[hgdef, ← Ideal.map_map, Ideal.map_pow, hJ]`. Establish `hlJB : (l : B.A) ∈ JJ B` using `Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)`.

Use `⟨{ Q := Qo, inl := inl, unit := ?_, I_eq := rfl, univ := ?_, surj := ?_, ker := ?_ }⟩` and prove the remaining obligations. Conclude with `hlu ⟨f, hfM⟩`. Introduce `C gC hu`. Establish `hMu : ∀ s : M, IsUnit (gC.f s)` using `fun s => locAway_units gC f hu s s.2`. Use `set lift : Localization M →+* C.A := IsLocalization.lift hMu with hliftdef`.

Establish `hla : ∀ x, lift (algebraMap B.A (Localization M) x) = gC.f x` using `IsLocalization.lift_eq hMu`. Establish `hδl : IsδMap DL C.D lift`. Establish `e : (W2.map lift).comp (deltaSectionToWittLengthTwo DL) = (deltaSectionToWittLengthTwo C.D).comp lift`. Apply `IsLocalization.ringHom_ext M` to reduce the goal to its premises. Use `RingHom.ext fun x => W2.ext rfl ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `lift (DL.δ (algebraMap B.A (Localization M) x)) = C.D.δ (lift (algebraMap B.A (Localization M) x))`. Rewrite using `[← hDL x, hla, hla, gC.f_δ]`. Introduce `x`. Conclude with `congrArg W2.snd (RingHom.congr_fun e x)`. Establish `hJle : J.map lift ≤ JJ C`.

Rewrite using `[hJdef, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast, hla]`. Conclude with `sup_le_sup_left (Ideal.span_le.2 (Set.singleton_subset_iff.2 (gC.f_I d hg.1))) _`. Use `haveI := C.complete`. Establish `hhaus : IsHausdorff (JJ C) C.A` using `inferInstance`. Take `⟨h, hh⟩` from `GlobalTheory.T.exists_ringHom_extend_isAdicCompletionMap _ Q C.A i J (JJ C) hi C.complete lift hJle`.

Establish `hhi : ∀ y, h (i y) = lift y` using `fun y => RingHom.congr_fun hh y`. Establish `hδh : IsδMap DQ C.D h`. Use `GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l Q C.A DQ C.D (J.map i) (JJ C) h ?_ ?_ hhaus ?_` and prove the remaining obligations. Rewrite using `[← map_natCast i]`. Conclude with `Ideal.mem_map_of_mem i hlJ`.

Rewrite using `[Ideal.map_map, hh]`. Conclude with `hJle`. Introduce `x n`. Take `⟨y, hy⟩` from `hi.surj x n`. Use `⟨i y, mem_δLocus.2 ?_, by rwa [← Ideal.map_pow]⟩` and prove the remaining obligations.

Rewrite using `[← hDQ y, hhi, hhi, hδl]`. Establish `hgC : h.comp g = gC.f` using `by rw [hgdef, ← RingHom.comp_assoc, hh, IsLocalization.lift_comp]`. Establish `hIC : ∀ x ∈ Ideal.span {g d}, h x ∈ C.I` using `fun x hx => (Ideal.span_le (I := C.I.comap h)).2 (Set.singleton_subset_iff.2 (by show h (g d) ∈ C.I`. Rewrite using `[← RingHom.comp_apply h g, hgC]`. Conclude with `gC.f_I d hg.1)) hx`.

Set `H : Hom Qo C` to `{ f := h f_δ := hδh f_I := hIC f_str := fun r x hx => by`. Take `⟨b, hb⟩` from `Ideal.Quotient.mk_surjective (B.str r)`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ x = Ideal.quotientMap _ g hIle (B.str r) at hx`. Rewrite `hx` using `[← hb, Ideal.quotientMap_mk, Ideal.Quotient.eq]`. Rewrite using `[← gC.f_str r b hb, Ideal.Quotient.eq, ← hgC, RingHom.comp_apply, ← map_sub]`.

Conclude with `hIC _ hx }`. Use `⟨H, Hom.ext' hgC, fun y hy => Hom.ext' ?_⟩` and prove the remaining obligations. Establish `hy' : y.f.comp g = gC.f` using `congrArg Hom.f hy`. Establish `hyi : y.f.comp i = h.comp i` using `IsLocalization.ringHom_ext M (hy'.trans hgC.symm)`. Conclude with `GlobalTheory.T.ringHom_eq_of_isAdicCompletionMap _ Q C.A i J (JJ C) hi hhaus y.f h (by rw [hyi, hh]; exact hJle) hyi`.

Introduce `x n`. Take `⟨y, hy⟩` from `hi.surj x n`. Take `⟨⟨b0, s⟩, hbs⟩` from `IsLocalization.mk'_surjective M y`. Simplify using `only at hbs`. Substitute `hbs` using the available equality.

Take `⟨k, t, hkt⟩` from `locAway_dvd_mod B.D f (JJ B) hlJB n s s.2`. Use `⟨k, b0 * t, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g f ^ k * x - g (b0 * t) ∈ ((JJ B) ^ n).map g`. Establish `hs : i (IsLocalization.mk' (Localization M) b0 s) * g s = g b0`. Rewrite using `[hgdef, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]`.

Establish `e : g f ^ k * x - g (b0 * t) = g f ^ k * (x - i (IsLocalization.mk' (Localization M) b0 s)) + i (IsLocalization.mk' (Localization M) b0 s) * g (f ^ k - s * t)`. Rewrite using `[map_sub, map_mul, map_mul, map_pow]`. Take the linear combination `(g t) * hs`. Rewrite using `[e]`. Use `Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem g hkt))` and prove the remaining obligations.

Rewrite using `[hJn]`. Conclude with `hy`. Introduce `b n hb`. Express the relevant statement in the definitionally equal form `g b ∈ ((JJ B) ^ n).map g at hb`. Rewrite `hb` using `[hJn]`.

Establish `h1` using `hi.ker _ n hb`. Rewrite `h1` using `[← hJ, ← Ideal.map_pow]`. Take `⟨⟨⟨j, hj⟩, s⟩, hjs⟩` from `(IsLocalization.mem_map_algebraMap_iff M (Localization M)).1 h1`. Rewrite `hjs` using `[← map_mul]`. Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists M (Localization M)).1 hjs`.

Establish `hcs : ((c : B.A) * (s : B.A)) * b ∈ JJ B ^ n`. Establish `e : ((c : B.A) * (s : B.A)) * b = (c : B.A) * j` using `by rw [← hc]; ring`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ hj`. Take `⟨k, t, hkt⟩` from `locAway_dvd_mod B.D f (JJ B) hlJB n ((c : B.A) * (s : B.A)) (M.mul_mem c.2 s.2)`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `e : f ^ k * b = (f ^ k - ((c : B.A) * (s : B.A)) * t) * b + t * (((c : B.A) * (s : B.A)) * b)` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ hkt) (Ideal.mul_mem_left _ _ hcs)`.
-/
theorem GenAway₂ : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A),
    GenAway B f d → Nonempty (LocP B f d) := by
  intro l _ R _ B f d hg
  set M := Submonoid.closure (Set.range fun m : ℕ => B.D.φ^[m] f) with hM
  have hfM : f ∈ M := Submonoid.subset_closure ⟨0, rfl⟩
  obtain ⟨DL, hDL⟩ := GlobalTheory.T.exists_deltaRingStructure_localization l B.A B.D M (locAway_φ_mem B.D f)
  obtain ⟨hIL, hdnz, N, hN⟩ := GlobalTheory.T.prismLocalization_span_nonZeroDivisor_bounded_torsion l R B f d hg M hfM
  set J : Ideal (Localization M) := Ideal.span {(l : Localization M)} ⊔
    Ideal.span {algebraMap B.A (Localization M) d} with hJdef
  have hJ : (JJ B).map (algebraMap B.A (Localization M)) = J := by
    rw [JJ, Ideal.map_sup, hIL, Ideal.map_span, Set.image_singleton, map_natCast]
  have hJfg : J.FG := Submodule.FG.sup (Submodule.fg_span_singleton _) (Submodule.fg_span_singleton _)
  obtain ⟨Q, _, i, hi⟩ := GlobalTheory.T.exists_isAdicCompletionMap_of_fg _ J hJfg
  have hlJ : (l : Localization M) ∈ J := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  obtain ⟨DQ, hDQ⟩ := GlobalTheory.T.exists_deltaRingStructure_adicCompletion l _ Q i J hi hlJ DL
  obtain ⟨hqnz, hqN⟩ := GlobalTheory.T.adic_completion_regular_and_torsion_bounded l _ Q i (algebraMap B.A (Localization M) d) N hdnz hN hi
  set g : B.A →+* Q := i.comp (algebraMap B.A (Localization M)) with hgdef
  have hgδ : ∀ x, g (B.D.δ x) = DQ.δ (g x) := fun x => by
    simp only [hgdef, RingHom.comp_apply]; rw [hDL x, hDQ]
  have hIg : B.I.map g = Ideal.span {g d} := by
    rw [hgdef, ← Ideal.map_map, hIL, Ideal.map_span, Set.image_singleton]; rfl
  have hIle : B.I ≤ (Ideal.span {g d}).comap g := Ideal.map_le_iff_le_comap.1 hIg.le
  have hJi : J.map i = Ideal.span {(l : Q)} ⊔ Ideal.span {g d} := by
    rw [hJdef, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      map_natCast]; rfl
  have hcomp : IsAdicComplete (Ideal.span {(l : Q)} ⊔ Ideal.span {g d}) Q := by
    have := hi.complete; rwa [hJi] at this
  have hgφ : g.comp B.D.φ = DQ.φ.comp g := RingHom.ext fun x => Delta.map_φ_of_map_δ B.D DQ g hgδ x
  have hlmem : (l : Q) ∈ Ideal.span {g d} ⊔ (Ideal.span {g d}).map DQ.φ := by
    have h := Ideal.mem_map_of_mem g B.l_mem
    have hgm : (B.I.map B.D.φ).map g = (B.I.map g).map DQ.φ := by
      rw [Ideal.map_map, Ideal.map_map, hgφ]
    rwa [map_natCast, Ideal.map_sup, hgm, hIg] at h
  have hbdd : ∃ n : ℕ, ∀ x : Q ⧸ Ideal.span {g d}, (∃ m : ℕ, (l : Q ⧸ Ideal.span {g d}) ^ m * x = 0) →
      (l : Q ⧸ Ideal.span {g d}) ^ n * x = 0 := by
    refine ⟨N, fun x ⟨m, hm⟩ => ?_⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm ⊢
    exact hqN y m hm
  let Qo : Obj l R :=
    { A := Q
      D := DQ
      I := Ideal.span {g d}
      inv := invertible_span_singleton hqnz
      complete := hcomp
      l_mem := hlmem
      bdd := hbdd
      str := (Ideal.quotientMap (Ideal.span {g d}) g hIle).comp B.str }
  let inl : Hom B Qo :=
    { f := g
      f_δ := hgδ
      f_I := fun x hx => hIle hx
      f_str := fun r x h => by
        show _ = Ideal.quotientMap (Ideal.span {g d}) g hIle (B.str r)
        rw [← h, Ideal.quotientMap_mk] }
  have hlu : ∀ s : M, IsUnit (g s) := fun s => (IsLocalization.map_units (Localization M) s).map i
  have hJn : ∀ n : ℕ, ((JJ B) ^ n).map g = (J ^ n).map i := fun n => by
    rw [hgdef, ← Ideal.map_map, Ideal.map_pow, hJ]
  have hlJB : (l : B.A) ∈ JJ B := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  refine ⟨{ Q := Qo, inl := inl, unit := ?_, I_eq := rfl, univ := ?_, surj := ?_, ker := ?_ }⟩
  · exact hlu ⟨f, hfM⟩
  · intro C gC hu
    have hMu : ∀ s : M, IsUnit (gC.f s) := fun s => locAway_units gC f hu s s.2
    set lift : Localization M →+* C.A := IsLocalization.lift hMu with hliftdef
    have hla : ∀ x, lift (algebraMap B.A (Localization M) x) = gC.f x := IsLocalization.lift_eq hMu
    have hδl : IsδMap DL C.D lift := by
      have e : (W2.map lift).comp (deltaSectionToWittLengthTwo DL) = (deltaSectionToWittLengthTwo C.D).comp lift := by
        apply IsLocalization.ringHom_ext M
        refine RingHom.ext fun x => W2.ext rfl ?_
        change lift (DL.δ (algebraMap B.A (Localization M) x)) =
          C.D.δ (lift (algebraMap B.A (Localization M) x))
        rw [← hDL x, hla, hla, gC.f_δ]
      intro x; exact congrArg W2.snd (RingHom.congr_fun e x)
    have hJle : J.map lift ≤ JJ C := by
      rw [hJdef, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
        map_natCast, hla]
      exact sup_le_sup_left (Ideal.span_le.2 (Set.singleton_subset_iff.2 (gC.f_I d hg.1))) _
    haveI := C.complete
    have hhaus : IsHausdorff (JJ C) C.A := inferInstance
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_ringHom_extend_isAdicCompletionMap _ Q C.A i J (JJ C) hi C.complete lift hJle
    have hhi : ∀ y, h (i y) = lift y := fun y => RingHom.congr_fun hh y
    have hδh : IsδMap DQ C.D h := by
      refine GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l Q C.A DQ C.D (J.map i) (JJ C) h ?_ ?_ hhaus ?_
      · rw [← map_natCast i]; exact Ideal.mem_map_of_mem i hlJ
      · rw [Ideal.map_map, hh]; exact hJle
      · intro x n
        obtain ⟨y, hy⟩ := hi.surj x n
        refine ⟨i y, mem_δLocus.2 ?_, by rwa [← Ideal.map_pow]⟩
        rw [← hDQ y, hhi, hhi, hδl]
    have hgC : h.comp g = gC.f := by rw [hgdef, ← RingHom.comp_assoc, hh, IsLocalization.lift_comp]
    have hIC : ∀ x ∈ Ideal.span {g d}, h x ∈ C.I := fun x hx =>
      (Ideal.span_le (I := C.I.comap h)).2 (Set.singleton_subset_iff.2 (by
        show h (g d) ∈ C.I
        rw [← RingHom.comp_apply h g, hgC]; exact gC.f_I d hg.1)) hx
    let H : Hom Qo C :=
      { f := h
        f_δ := hδh
        f_I := hIC
        f_str := fun r x hx => by
          obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (B.str r)
          change Ideal.Quotient.mk _ x = Ideal.quotientMap _ g hIle (B.str r) at hx
          rw [← hb, Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
          rw [← gC.f_str r b hb, Ideal.Quotient.eq, ← hgC, RingHom.comp_apply, ← map_sub]
          exact hIC _ hx }
    refine ⟨H, Hom.ext' hgC, fun y hy => Hom.ext' ?_⟩
    have hy' : y.f.comp g = gC.f := congrArg Hom.f hy
    have hyi : y.f.comp i = h.comp i := IsLocalization.ringHom_ext M (hy'.trans hgC.symm)
    exact GlobalTheory.T.ringHom_eq_of_isAdicCompletionMap _ Q C.A i J (JJ C) hi hhaus y.f h (by rw [hyi, hh]; exact hJle) hyi
  · intro x n
    obtain ⟨y, hy⟩ := hi.surj x n
    obtain ⟨⟨b0, s⟩, hbs⟩ := IsLocalization.mk'_surjective M y
    dsimp only at hbs
    subst hbs
    obtain ⟨k, t, hkt⟩ := locAway_dvd_mod B.D f (JJ B) hlJB n s s.2
    refine ⟨k, b0 * t, ?_⟩
    change g f ^ k * x - g (b0 * t) ∈ ((JJ B) ^ n).map g
    have hs : i (IsLocalization.mk' (Localization M) b0 s) * g s = g b0 := by
      rw [hgdef, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
    have e : g f ^ k * x - g (b0 * t) = g f ^ k * (x - i (IsLocalization.mk' (Localization M) b0 s)) +
        i (IsLocalization.mk' (Localization M) b0 s) * g (f ^ k - s * t) := by
      rw [map_sub, map_mul, map_mul, map_pow]; linear_combination (g t) * hs
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem g hkt))
    rw [hJn]; exact hy
  · intro b n hb
    change g b ∈ ((JJ B) ^ n).map g at hb
    rw [hJn] at hb
    have h1 := hi.ker _ n hb
    rw [← hJ, ← Ideal.map_pow] at h1
    obtain ⟨⟨⟨j, hj⟩, s⟩, hjs⟩ := (IsLocalization.mem_map_algebraMap_iff M (Localization M)).1 h1
    rw [← map_mul] at hjs
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M (Localization M)).1 hjs
    have hcs : ((c : B.A) * (s : B.A)) * b ∈ JJ B ^ n := by
      have e : ((c : B.A) * (s : B.A)) * b = (c : B.A) * j := by rw [← hc]; ring
      rw [e]; exact Ideal.mul_mem_left _ _ hj
    obtain ⟨k, t, hkt⟩ := locAway_dvd_mod B.D f (JJ B) hlJB n ((c : B.A) * (s : B.A)) (M.mul_mem c.2 s.2)
    refine ⟨k, ?_⟩
    have e : f ^ k * b = (f ^ k - ((c : B.A) * (s : B.A)) * t) * b + t * (((c : B.A) * (s : B.A)) * b) := by ring
    rw [e]; exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hkt) (Ideal.mul_mem_left _ _ hcs)

end GlobalTheory.BSP
