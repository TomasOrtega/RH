import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DualInter

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

noncomputable def hfL (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := hf L Hm x y
  map_add' a b := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [hf, Finset.mul_sum, mul_assoc]

noncomputable def hfR (x : Fin n → E) : (Fin n → E) →+ E where
  toFun y := hf L Hm x y
  map_add' a b := by simp [hf, mul_add, Finset.sum_add_distrib]
  map_zero' := by simp [hf]

/- English proof (translation)
The claim follows from `(hfL L Hm y).map_sub a b`.
-/
theorem sub_l (a b y : Fin n → E) : hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y :=
  (hfL L Hm y).map_sub a b

/- English proof (translation)
The claim follows from `(hfL L Hm y).map_smul c a`.
-/
theorem smul_l (c : E) (a y : Fin n → E) : hf L Hm (c • a) y = c * hf L Hm a y :=
  (hfL L Hm y).map_smul c a

/- English proof (translation)
The claim follows from `map_sum (hfL L Hm y) a s`.
-/
theorem sum_l {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y :=
  map_sum (hfL L Hm y) a s

/- English proof (translation)
The claim follows from `(hfR L Hm x).map_sub a b`.
-/
theorem sub_r (x a b : Fin n → E) : hf L Hm x (a - b) = hf L Hm x a - hf L Hm x b :=
  (hfR L Hm x).map_sub a b

/- English proof (translation)
The claim follows from `map_sum (hfR L Hm x) a s`.
-/
theorem sum_r {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (x : Fin n → E) :
    hf L Hm x (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm x (a i) :=
  map_sum (hfR L Hm x) a s

/- English proof (translation)
Simplify using `only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem smul_r (c : E) (x a : Fin n → E) : hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {L Hm}

/- English proof (translation)
Establish `hH : ∀ i j, L.cj (Hm i j) = Hm j i` using `fun i j => congrFun (congrFun h.1 j) i`. Simplify using `only [hf, map_sum, map_mul, hH, L.cj_cj]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem cj_hf (h : IsHermND L Hm) (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by
  have hH : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h.1 j) i
  simp only [hf, map_sum, map_mul, hH, L.cj_cj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `h1 : Hm.mulVec (fun j => L.cj (y j)) = 0`. Use function extensionality and compare the values at `i`. Use `hy (Pi.single i 1)` as an intermediate fact. Simplify `this` using `[hf, Pi.single_apply, Finset.sum_ite_eq, Matrix.mulVec, dotProduct, ite_mul]`. Establish `h2 : (fun j => L.cj (y j)) = 0`.

Use `congrArg (Hm⁻¹.mulVec) h1` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.2, Matrix.one_mulVec, Matrix.mulVec_zero]`. Then use the resulting hypothesis. Use function extensionality and compare the values at `j`. Conclude with `L.cj.injective (by simpa using congrFun h2 j)`.
-/
theorem eq_zero_of_hf (h : IsHermND L Hm) {y : Fin n → E} (hy : ∀ x, hf L Hm x y = 0) : y = 0 := by
  have h1 : Hm.mulVec (fun j => L.cj (y j)) = 0 := by
    funext i
    have := hy (Pi.single i 1)
    simpa [hf, Pi.single_apply, Finset.sum_ite_eq, Matrix.mulVec, dotProduct, ite_mul] using this
  have h2 : (fun j => L.cj (y j)) = 0 := by
    have := congrArg (Hm⁻¹.mulVec) h1
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.2, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
  funext j
  exact L.cj.injective (by simpa using congrFun h2 j)

/- English proof (translation)
Introduce `x hx` and use `(Submodule.span_le (p := LinearMap.ker (hfL L Hm y))).2 hy hx`.
-/
theorem hf_eq_zero_of_span {S : Set (Fin n → E)} {y : Fin n → E} (hy : ∀ x ∈ S, hf L Hm x y = 0) :
    ∀ x ∈ Submodule.span E S, hf L Hm x y = 0 := fun x hx =>
  (Submodule.span_le (p := LinearMap.ker (hfL L Hm y))).2 hy hx

variable [IsNonarchimedeanLocalField F]

/- English proof (translation)
Use `L.free` as an intermediate fact. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [L.rank]; omega)`. Establish `hx : IsAlgebraic 𝒪[F] x` using `(IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic x)`. Take `⟨d, hd0, hd⟩` from `hx.exists_integral_multiple`. Use `⟨algebraMap F E d, (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 d.2, (IsUnit.mk0 (d : F) fun h => hd0 (Subtype.ext h)).map _, (L.O_def _).2 ?_⟩` and prove the remaining obligations.

Rewrite `hd` using `[Algebra.smul_def]`. Then use the resulting hypothesis.
-/
theorem exists_denom (L : LocE F E) (x : E) : ∃ d ∈ L.O, IsUnit d ∧ d * x ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have hx : IsAlgebraic 𝒪[F] x :=
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hd⟩ := hx.exists_integral_multiple
  refine ⟨algebraMap F E d, (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 d.2,
    (IsUnit.mk0 (d : F) fun h => hd0 (Subtype.ext h)).map _, (L.O_def _).2 ?_⟩
  rwa [Algebra.smul_def] at hd

/- English proof (translation)
Proceed by induction on `Λ, hΛ using Submodule.fg_induction with`. Consider the case `singleton v`. Take `⟨d, h1, h2, h3⟩` from `exists_denom L (hf L Hm v y)`. Use `⟨d, h1, h2, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hx`.

Establish `: hf L Hm (a • v) y = a * hf L Hm v y` using `smul_l L Hm a v y`. Rewrite using `[this, mul_left_comm]`. Conclude with `L.O.mul_mem a.2 h3`. Consider the case `sup A B _ _ hA hB`. Take `⟨d, h1, h2, h3⟩` from `hA`.

Take `⟨e, k1, k2, k3⟩` from `hB`. Use `⟨d * e, L.O.mul_mem h1 k1, h2.mul k2, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hx`. Establish `: hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y` using `(hfL L Hm y).map_add a b`. Rewrite using `[this, show d * e * (hf L Hm a y + hf L Hm b y) = e * (d * hf L Hm a y) + d * (e * hf L Hm b y) by ring]`.

Conclude with `L.O.add_mem (L.O.mul_mem k1 (h3 a ha)) (L.O.mul_mem h1 (k3 b hb))`.
-/
theorem exists_denom_fg {Λ : Submodule L.O (Fin n → E)} (hΛ : Λ.FG) (y : Fin n → E) :
    ∃ d ∈ L.O, IsUnit d ∧ ∀ x ∈ Λ, d * hf L Hm x y ∈ L.O := by
  induction Λ, hΛ using Submodule.fg_induction with
  | singleton v =>
    obtain ⟨d, h1, h2, h3⟩ := exists_denom L (hf L Hm v y)
    refine ⟨d, h1, h2, fun x hx => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have : hf L Hm (a • v) y = a * hf L Hm v y := smul_l L Hm a v y
    rw [this, mul_left_comm]
    exact L.O.mul_mem a.2 h3
  | sup A B _ _ hA hB =>
    obtain ⟨d, h1, h2, h3⟩ := hA
    obtain ⟨e, k1, k2, k3⟩ := hB
    refine ⟨d * e, L.O.mul_mem h1 k1, h2.mul k2, fun x hx => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := (hfL L Hm y).map_add a b
    rw [this, show d * e * (hf L Hm a y + hf L Hm b y)
      = e * (d * hf L Hm a y) + d * (e * hf L Hm b y) by ring]
    exact L.O.add_mem (L.O.mul_mem k1 (h3 a ha)) (L.O.mul_mem h1 (k3 b hb))

/- English proof (translation)
Use `L.free` as an intermediate fact. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [L.rank]; omega)`. Establish `: IsArtinianRing E` using `IsArtinianRing.of_finite F E`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Establish `hP : IsPrincipalIdealRing L.O` using `(GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1`.

Take `⟨d, -, hd, hdx⟩` from `exists_denom_fg (Hm := Hm) hΛ.1.1 y`. Set `I : Ideal L.O` to `{ carrier := {r | ∃ x ∈ Λ, (r : E) = d * hf L Hm x y} zero_mem' := ⟨0, Λ.zero_mem, by simp [hf]⟩ add_mem' := by`. Introduce and unpack `r s ⟨a, ha, hr⟩ ⟨b, hb, hs⟩`. Use `⟨a + b, Λ.add_mem ha hb, ?_⟩` and prove the remaining obligations. Establish `: hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y` using `(hfL L Hm y).map_add a b`.

Rewrite using `[this, Subring.coe_add, hr, hs, mul_add]`. Use the proof step `smul_mem' := by`. Introduce and unpack `s r ⟨a, ha, hr⟩`. Use `⟨s • a, Λ.smul_mem s ha, ?_⟩` and prove the remaining obligations. Establish `: hf L Hm (s • a) y = s * hf L Hm a y` using `smul_l L Hm s a y`.

Rewrite using `[this, smul_eq_mul, Subring.coe_mul, hr, mul_left_comm] }`. Take `⟨g, hg⟩` from `(IsPrincipalIdealRing.principal I).principal`. Take `⟨c, hc, hgc⟩ : g ∈ I` from `by rw [hg]; exact Submodule.mem_span_singleton_self g`. Establish `hdiv : ∀ x ∈ Λ, ∃ r ∈ L.O, hf L Hm x y = r * hf L Hm c y`. Introduce `x hx`.

Establish `: (⟨_, hdx x hx⟩ : L.O) ∈ I` using `⟨x, hx, rfl⟩`. Rewrite `this` using `[hg]`. Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 this`. Establish `hr' : (r : E) * g = d * hf L Hm x y` using `congrArg Subtype.val hr`. Use `⟨r, r.2, hd.mul_left_cancel ?_⟩` and prove the remaining obligations.

Rewrite using `[← hr', hgc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hu : IsUnit (hf L Hm c y)`. Use `IsArtinianRing.isUnit_of_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_right.2 ?_)` and prove the remaining obligations. Introduce `s hs`.

Establish `h1 : L.cj s • y = 0` using `eq_zero_of_hf h fun x => hf_eq_zero_of_span (S := Λ) (fun z hz => by`. Take `⟨r, -, hr⟩` from `hdiv z hz`. Rewrite using `[smul_r, L.cj_cj, hr, mul_left_comm, hs, mul_zero]) x (by rw [hΛ.1.2]; trivial)`. Conclude with `L.cj.injective (by simpa using hy _ h1)`. Take `⟨u, hu'⟩` from `hu.exists_left_inv`.

Use `⟨L.cj u, (IsUnit.of_mul_eq_one _ hu').map _, (hΛ.2 _).1 fun x hx => ?_, c, hc, ?_⟩` and prove the remaining obligations. Take `⟨r, hr0, hr⟩` from `hdiv x hx`. Rewrite using `[smul_r, L.cj_cj, hr, mul_left_comm, hu', mul_one]`. Conclude with `hr0`. Rewrite using `[← cj_hf h, smul_r, L.cj_cj, hu', map_one]`.
-/
theorem exists_primitive [CharZero F] (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsSD L Hm Λ) {y : Fin n → E} (hy : ∀ s : E, s • y = 0 → s = 0) :
    ∃ t : E, IsUnit t ∧ t • y ∈ Λ ∧ ∃ c ∈ Λ, hf L Hm (t • y) c = 1 := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hP : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  obtain ⟨d, -, hd, hdx⟩ := exists_denom_fg (Hm := Hm) hΛ.1.1 y
  let I : Ideal L.O :=
    { carrier := {r | ∃ x ∈ Λ, (r : E) = d * hf L Hm x y}
      zero_mem' := ⟨0, Λ.zero_mem, by simp [hf]⟩
      add_mem' := by
        rintro r s ⟨a, ha, hr⟩ ⟨b, hb, hs⟩
        refine ⟨a + b, Λ.add_mem ha hb, ?_⟩
        have : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := (hfL L Hm y).map_add a b
        rw [this, Subring.coe_add, hr, hs, mul_add]
      smul_mem' := by
        rintro s r ⟨a, ha, hr⟩
        refine ⟨s • a, Λ.smul_mem s ha, ?_⟩
        have : hf L Hm (s • a) y = s * hf L Hm a y := smul_l L Hm s a y
        rw [this, smul_eq_mul, Subring.coe_mul, hr, mul_left_comm] }
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal I).principal
  obtain ⟨c, hc, hgc⟩ : g ∈ I := by rw [hg]; exact Submodule.mem_span_singleton_self g
  have hdiv : ∀ x ∈ Λ, ∃ r ∈ L.O, hf L Hm x y = r * hf L Hm c y := by
    intro x hx
    have : (⟨_, hdx x hx⟩ : L.O) ∈ I := ⟨x, hx, rfl⟩
    rw [hg] at this
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
    have hr' : (r : E) * g = d * hf L Hm x y := congrArg Subtype.val hr
    refine ⟨r, r.2, hd.mul_left_cancel ?_⟩
    rw [← hr', hgc]; ring
  have hu : IsUnit (hf L Hm c y) := by
    refine IsArtinianRing.isUnit_of_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_right.2 ?_)
    intro s hs
    have h1 : L.cj s • y = 0 := eq_zero_of_hf h fun x =>
      hf_eq_zero_of_span (S := Λ) (fun z hz => by
        obtain ⟨r, -, hr⟩ := hdiv z hz
        rw [smul_r, L.cj_cj, hr, mul_left_comm, hs, mul_zero]) x (by rw [hΛ.1.2]; trivial)
    exact L.cj.injective (by simpa using hy _ h1)
  obtain ⟨u, hu'⟩ := hu.exists_left_inv
  refine ⟨L.cj u, (IsUnit.of_mul_eq_one _ hu').map _, (hΛ.2 _).1 fun x hx => ?_, c, hc, ?_⟩
  · obtain ⟨r, hr0, hr⟩ := hdiv x hx
    rw [smul_r, L.cj_cj, hr, mul_left_comm, hu', mul_one]
    exact hr0
  · rw [← cj_hf h, smul_r, L.cj_cj, hu', map_one]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact ⟨y, y, fun i => i.elim0, fun i => i.elim0, rfl, fun i => i.elim0⟩`. Consider the case `succ m ih`. Take `⟨b, c, hb, hc, hspan, hbc⟩` from `ih (Fin.tail y) (hy.comp _ (Fin.succ_injective m))`. Use `set w := ∑ j, hf L Hm (y 0) (c j) • b j with hw`.

Establish `hwm : w ∈ Submodule.span E (Set.range b)` using `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Establish `hz : ∀ j, hf L Hm (y 0 - w) (c j) = 0` using `fun j => by`. Simplify using `[hw, sub_l, sum_l, smul_l, hbc]`. Take `⟨t, ht, htm, c', hc', htc⟩` from `exists_primitive h hΛ (y := y 0 - w) (fun s hs => by`. Use `hy.eq_zero_of_smul_mem_span 0 s ?_` and prove the remaining obligations.

Rewrite `hs` using `[smul_sub, sub_eq_zero]`. Rewrite using `[hs]`. Use `Submodule.smul_mem _ _ (Submodule.span_mono ?_ (hspan ▸ hwm))` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨j.succ, by simp, rfl⟩)`.

Establish `hc0 : c' - ∑ j, hf L Hm c' (b j) • c j ∈ Λ` using `Λ.sub_mem hc' (Λ.sum_mem fun j _ => Λ.smul_mem ⟨_, (hΛ.2 _).2 (hb j) _ hc'⟩ (hc j))`. Use `⟨Fin.cons (t • (y 0 - w)) b, Fin.cons (c' - ∑ j, hf L Hm c' (b j) • c j) c, fun i => Fin.cases htm hb i, fun i => Fin.cases hc0 hc i, ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.range_cons, Fin.range_fin_succ y, Submodule.span_insert, Submodule.span_insert, ← hspan, ← Submodule.span_singleton_smul_eq ht (y 0)]`. Establish `hwt` using `Submodule.smul_mem _ t hwm`. Rewrite using `[smul_sub]`.

Apply the tactic sequence `refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right) <;>`. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)) (Submodule.mem_sup_right hwt)`. Use `Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self (t • y 0 - t • w))) (Submodule.mem_sup_right hwt)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Simplify using `only [Fin.cons_zero, sub_r, sum_r, smul_r, htc]`. Simplify using `[smul_l L Hm t, hz]`. Simplify using `[smul_l L Hm t, hz, (Fin.succ_ne_zero j).symm]`. Simplify using `[sub_r, sum_r, smul_r, hbc, cj_hf h]`.

Simplify using `[hbc]`.
-/
theorem exists_dual_family [CharZero F] (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsSD L Hm Λ) (m : ℕ) (y : Fin m → Fin n → E) (hy : LinearIndependent E y) :
    ∃ b c : Fin m → Fin n → E, (∀ i, b i ∈ Λ) ∧ (∀ j, c j ∈ Λ) ∧
      Submodule.span E (Set.range b) = Submodule.span E (Set.range y) ∧
      ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0 := by
  induction m with
  | zero => exact ⟨y, y, fun i => i.elim0, fun i => i.elim0, rfl, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨b, c, hb, hc, hspan, hbc⟩ := ih (Fin.tail y) (hy.comp _ (Fin.succ_injective m))
    set w := ∑ j, hf L Hm (y 0) (c j) • b j with hw
    have hwm : w ∈ Submodule.span E (Set.range b) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hz : ∀ j, hf L Hm (y 0 - w) (c j) = 0 := fun j => by
      simp [hw, sub_l, sum_l, smul_l, hbc]
    obtain ⟨t, ht, htm, c', hc', htc⟩ := exists_primitive h hΛ (y := y 0 - w) (fun s hs => by
      refine hy.eq_zero_of_smul_mem_span 0 s ?_
      rw [smul_sub, sub_eq_zero] at hs
      rw [hs]
      refine Submodule.smul_mem _ _ (Submodule.span_mono ?_ (hspan ▸ hwm))
      rintro _ ⟨j, rfl⟩
      exact ⟨j.succ, by simp, rfl⟩)
    have hc0 : c' - ∑ j, hf L Hm c' (b j) • c j ∈ Λ :=
      Λ.sub_mem hc' (Λ.sum_mem fun j _ => Λ.smul_mem ⟨_, (hΛ.2 _).2 (hb j) _ hc'⟩ (hc j))
    refine ⟨Fin.cons (t • (y 0 - w)) b, Fin.cons (c' - ∑ j, hf L Hm c' (b j) • c j) c,
      fun i => Fin.cases htm hb i, fun i => Fin.cases hc0 hc i, ?_, fun i j => ?_⟩
    · rw [Fin.range_cons, Fin.range_fin_succ y, Submodule.span_insert, Submodule.span_insert,
        ← hspan, ← Submodule.span_singleton_smul_eq ht (y 0)]
      have hwt := Submodule.smul_mem _ t hwm
      rw [smul_sub]
      refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right) <;>
        rw [Submodule.span_singleton_le_iff_mem]
      · exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
          (Submodule.mem_sup_right hwt)
      · have := Submodule.add_mem _ (Submodule.mem_sup_left
          (Submodule.mem_span_singleton_self (t • y 0 - t • w))) (Submodule.mem_sup_right hwt)
        rwa [sub_add_cancel] at this
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero, sub_r, sum_r, smul_r, htc]
        simp [smul_l L Hm t, hz]
      · simp [smul_l L Hm t, hz, (Fin.succ_ne_zero j).symm]
      · simp [sub_r, sum_r, smul_r, hbc, cj_hf h]
      · simp [hbc]

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L n Hm h Λ hΛ m y hy`. Take `⟨b, c, hb, hc, hspan, hbc⟩` from `exists_dual_family h hΛ m y hy`. Rewrite using `[← hspan]`. Use `set Y := Submodule.span E (Set.range b) with hY`. Establish `hbY : ∀ j, b j ∈ Y` using `fun j => Submodule.subset_span ⟨j, rfl⟩`.

Establish `hsym : ∀ x v, hf L Hm x v = 0 → hf L Hm v x = 0` using `fun x v hx => by`. Rewrite using `[← cj_hf h, hx, map_zero]`. Establish `hperp : ∀ x, (∀ i, hf L Hm (b i) x = 0) → x ∈ perp L Hm Y` using `fun x hx v hv => hsym _ _ (hf_eq_zero_of_span (by rintro _ ⟨i, rfl⟩; exact hx i) v hv)`. Establish `hproj : ∀ x, x - ∑ j, hf L Hm x (b j) • c j ∈ perp L Hm Y` using `fun x => hperp _ fun i => by simp [sub_r, sum_r, smul_r, hbc, cj_hf h]`. Establish `hadj : ∀ x v, hf L Hm x (v - ∑ j, hf L Hm v (c j) • b j) = hf L Hm (x - ∑ j, hf L Hm x (b j) • c j) v` using `fun x v => by`.

Simplify using `[sub_r, sum_r, smul_r, sub_l, sum_l, smul_l, cj_hf h, mul_comm]`. Establish `hsum : ∀ v, ∑ j, hf L Hm v (c j) • b j ∈ Y` using `fun v => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbY j)`. Establish `hpp : ∀ v, (∀ x ∈ perp L Hm Y, hf L Hm x v = 0) → v = ∑ j, hf L Hm v (c j) • b j` using `fun v hv => sub_eq_zero.1 (eq_zero_of_hf h fun x => by rw [hadj]; exact hv _ (hproj x))`. Use `⟨?_, fun v => ⟨fun hv => ?_, ?_⟩, fun v => ⟨fun hv => ?_, ?_⟩, b, c, ?_, hc, hbc⟩` and prove the remaining obligations. Use extensionality with `v`.

Use `⟨fun hv => ?_, fun hv x hx => hsym _ _ (hx v hv)⟩` and prove the remaining obligations. Rewrite using `[hpp v fun x hx => hsym _ _ (hv x hx)]`. Conclude with `hsum v`. Use `⟨v - ∑ j, hf L Hm v (c j) • b j, (hΛ.2 _).1 fun x hx => ?_, by simpa using hsum v⟩` and prove the remaining obligations. Rewrite using `[hadj]`.

Use `hv _ (Λ.sub_mem hx (Λ.sum_mem fun j _ => ?_)) (hproj x)` and prove the remaining obligations. Conclude with `Λ.smul_mem ⟨_, (hΛ.2 _).2 (hb j) _ hx⟩ (hc j)`. Introduce and unpack `⟨a, ha, hva⟩ x hx hxp`. Use `hxp _ hva` as an intermediate fact. Rewrite `this` using `[sub_r, sub_eq_zero]`.

Rewrite using `[this]`. Conclude with `(hΛ.2 _).2 ha x hx`. Use `⟨_, Λ.sum_mem fun j _ => ?_, hproj v⟩` and prove the remaining obligations. Establish `: hf L Hm v (b j) ∈ L.O`. Rewrite using `[← cj_hf h]`.

Conclude with `GlobalTheory.UnramOrder.cj_mem L (hv _ (hb j) (hbY j))`. Conclude with `Λ.smul_mem ⟨_, this⟩ (hc j)`. Introduce and unpack `⟨a, ha, hva⟩ x hx hxp`. Use `hsym _ _ (hva x hxp)` as an intermediate fact. Rewrite `this` using `[sub_r, sub_eq_zero]`.

Rewrite using `[this]`. Conclude with `(hΛ.2 _).2 ha x hx`. Use `le_antisymm ?_ (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `v ⟨hv, hvY⟩`. Rewrite using `[hpp v fun x hx => hx v hvY]`.

Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Conclude with `Submodule.smul_mem (Submodule.span L.O (Set.range b)) ⟨_, (hΛ.2 _).2 (hc j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨hb j, hbY j⟩`.
-/
theorem dual_inter : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → perp L Hm (perp L Hm (Submodule.span E (Set.range y))) = (Submodule.span E (Set.range y)) ∧ (∀ v, (∀ x ∈ Λ, x ∈ perp L Hm (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ (Submodule.span E (Set.range y))) ∧ (∀ v, (∀ x ∈ Λ, x ∈ (Submodule.span E (Set.range y)) → hf L Hm x v ∈ L.O) ↔ ∃ a ∈ Λ, v - a ∈ perp L Hm (Submodule.span E (Set.range y))) ∧ ∃ b : Fin m → Fin n → E, ∃ c : Fin m → Fin n → E, Λ ⊓ (Submodule.span E (Set.range y)).restrictScalars L.O = Submodule.span L.O (Set.range b) ∧ (∀ j, c j ∈ Λ) ∧ ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0 := by
  intro F _ _ _ _ _ E _ _ _ L n Hm h Λ hΛ m y hy
  obtain ⟨b, c, hb, hc, hspan, hbc⟩ := exists_dual_family h hΛ m y hy
  rw [← hspan]
  set Y := Submodule.span E (Set.range b) with hY
  have hbY : ∀ j, b j ∈ Y := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hsym : ∀ x v, hf L Hm x v = 0 → hf L Hm v x = 0 := fun x v hx => by
    rw [← cj_hf h, hx, map_zero]
  have hperp : ∀ x, (∀ i, hf L Hm (b i) x = 0) → x ∈ perp L Hm Y := fun x hx v hv =>
    hsym _ _ (hf_eq_zero_of_span (by rintro _ ⟨i, rfl⟩; exact hx i) v hv)
  have hproj : ∀ x, x - ∑ j, hf L Hm x (b j) • c j ∈ perp L Hm Y := fun x =>
    hperp _ fun i => by simp [sub_r, sum_r, smul_r, hbc, cj_hf h]
  have hadj : ∀ x v, hf L Hm x (v - ∑ j, hf L Hm v (c j) • b j)
      = hf L Hm (x - ∑ j, hf L Hm x (b j) • c j) v := fun x v => by
    simp [sub_r, sum_r, smul_r, sub_l, sum_l, smul_l, cj_hf h, mul_comm]
  have hsum : ∀ v, ∑ j, hf L Hm v (c j) • b j ∈ Y := fun v =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbY j)
  have hpp : ∀ v, (∀ x ∈ perp L Hm Y, hf L Hm x v = 0) → v = ∑ j, hf L Hm v (c j) • b j :=
    fun v hv => sub_eq_zero.1 (eq_zero_of_hf h fun x => by rw [hadj]; exact hv _ (hproj x))
  refine ⟨?_, fun v => ⟨fun hv => ?_, ?_⟩, fun v => ⟨fun hv => ?_, ?_⟩, b, c, ?_, hc, hbc⟩
  · ext v
    refine ⟨fun hv => ?_, fun hv x hx => hsym _ _ (hx v hv)⟩
    rw [hpp v fun x hx => hsym _ _ (hv x hx)]
    exact hsum v
  · refine ⟨v - ∑ j, hf L Hm v (c j) • b j, (hΛ.2 _).1 fun x hx => ?_, by simpa using hsum v⟩
    rw [hadj]
    refine hv _ (Λ.sub_mem hx (Λ.sum_mem fun j _ => ?_)) (hproj x)
    exact Λ.smul_mem ⟨_, (hΛ.2 _).2 (hb j) _ hx⟩ (hc j)
  · rintro ⟨a, ha, hva⟩ x hx hxp
    have := hxp _ hva
    rw [sub_r, sub_eq_zero] at this
    rw [this]
    exact (hΛ.2 _).2 ha x hx
  · refine ⟨_, Λ.sum_mem fun j _ => ?_, hproj v⟩
    have : hf L Hm v (b j) ∈ L.O := by
      rw [← cj_hf h]
      exact GlobalTheory.UnramOrder.cj_mem L (hv _ (hb j) (hbY j))
    exact Λ.smul_mem ⟨_, this⟩ (hc j)
  · rintro ⟨a, ha, hva⟩ x hx hxp
    have := hsym _ _ (hva x hxp)
    rw [sub_r, sub_eq_zero] at this
    rw [this]
    exact (hΛ.2 _).2 ha x hx
  · refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro v ⟨hv, hvY⟩
      rw [hpp v fun x hx => hx v hvY]
      refine Submodule.sum_mem _ fun j _ => ?_
      exact Submodule.smul_mem (Submodule.span L.O (Set.range b))
        ⟨_, (hΛ.2 _).2 (hc j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)
    · rintro _ ⟨j, rfl⟩
      exact ⟨hb j, hbY j⟩

end GlobalTheory.HL.DualInter
