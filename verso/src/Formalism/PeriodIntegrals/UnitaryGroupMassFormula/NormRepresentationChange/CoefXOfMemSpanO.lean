import Mathlib
import Formalism.PeriodIntegrals.PairValDefs
import Formalism.PeriodIntegrals.NormRepChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section IntP

variable {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E))

def IntP (x : D.host.E) : Prop :=
  ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (s : D.host.E) * x = o

/- English proof (translation)
Introduce `h` and use `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)`.
-/
theorem one_not_mem_P : (1 : 𝓞 D.host.E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

/- English proof (translation)
Introduce `h` and use `(P.isPrime.mem_or_mem h).elim hs ht`.
-/
theorem mul_not_mem_P {s t : 𝓞 D.host.E} (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) : s * t ∉ P.asIdeal :=
  fun h => (P.isPrime.mem_or_mem h).elim hs ht

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_not_mem_P P, o, by simp⟩`.
-/
theorem intP_O (o : 𝓞 D.host.E) : IntP P (o : D.host.E) := ⟨1, one_not_mem_P P, o, by simp⟩

/- English proof (translation)
Take `⟨s1, hs1, o1, h1⟩` from `hx`. Take `⟨s2, hs2, o2, h2⟩` from `hy`. Use `⟨s1 * s2, mul_not_mem_P P hs1 hs2, o1 * s2 + o2 * s1, ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `(s2 : D.host.E) * h1 + (s1 : D.host.E) * h2`.
-/
theorem intP_add {x y : D.host.E} (hx : IntP P x) (hy : IntP P y) : IntP P (x + y) := by
  obtain ⟨s1, hs1, o1, h1⟩ := hx
  obtain ⟨s2, hs2, o2, h2⟩ := hy
  refine ⟨s1 * s2, mul_not_mem_P P hs1 hs2, o1 * s2 + o2 * s1, ?_⟩
  push_cast
  linear_combination (s2 : D.host.E) * h1 + (s1 : D.host.E) * h2

/- English proof (translation)
Take `⟨s1, hs1, o1, h1⟩` from `hx`. Take `⟨s2, hs2, o2, h2⟩` from `hy`. Use `⟨s1 * s2, mul_not_mem_P P hs1 hs2, o1 * o2, ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `((s2 : D.host.E) * y) * h1 + (o1 : D.host.E) * h2`.
-/
theorem valuation_coeff_mul_nonneg {x y : D.host.E} (hx : IntP P x) (hy : IntP P y) : IntP P (x * y) := by
  obtain ⟨s1, hs1, o1, h1⟩ := hx
  obtain ⟨s2, hs2, o2, h2⟩ := hy
  refine ⟨s1 * s2, mul_not_mem_P P hs1 hs2, o1 * o2, ?_⟩
  push_cast
  linear_combination ((s2 : D.host.E) * y) * h1 + (o1 : D.host.E) * h2

/- English proof (translation)
Use `valuation_coeff_mul_nonneg P (intP_O P (-1)) hx` as an intermediate fact. Simplify using `using this`.
-/
theorem isIntegralAt_neg {x : D.host.E} (hx : IntP P x) : IntP P (-x) := by
  have := valuation_coeff_mul_nonneg P (intP_O P (-1)) hx
  simpa using this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using intP_O P 0`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi]`. Conclude with `intP_add P (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem intP_sum {ι : Type*} (s : Finset ι) (f : ι → D.host.E) (h : ∀ i ∈ s, IntP P (f i)) :
    IntP P (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using intP_O P 0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact intP_add P (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Take `⟨s, hs, o, h⟩` from `hx`. Establish `e1 : algebraMap (𝓞 D.host.E) D.host.E s = (s : D.host.E)` using `rfl`. Establish `e2 : algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E)` using `rfl`. Use `congrArg (P.valuation D.host.E) h` as an intermediate fact. Rewrite `this` using `[map_mul, ← e1, ← e2, P.valuation_of_algebraMap, P.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.mpr hs, one_mul]`.

Rewrite using `[this]`. Conclude with `P.intValuation_le_one o`.
-/
theorem valuation_le_one_of_isIntegralAt {x : D.host.E} (hx : IntP P x) : P.valuation D.host.E x ≤ 1 := by
  obtain ⟨s, hs, o, h⟩ := hx
  have e1 : algebraMap (𝓞 D.host.E) D.host.E s = (s : D.host.E) := rfl
  have e2 : algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) := rfl
  have := congrArg (P.valuation D.host.E) h
  rw [map_mul, ← e1, ← e2, P.valuation_of_algebraMap, P.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hs, one_mul] at this
  rw [this]
  exact P.intValuation_le_one o

end IntP

section Loc

variable {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E))

def LP (L : Submodule (𝓞 D.host.E) (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V :=
  haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L

/- English proof (translation)
Unfold `LP Formalism.HermitianLatticesTheory.localization₂ Formalism.HermitianLatticesTheory.locS`. Simplify using `only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]`. Both sides reduce to the same expression.
-/
theorem mem_LP {L : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} :
    x ∈ LP P L ↔ ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • x ∈ L := by
  unfold LP Formalism.HermitianLatticesTheory.localization₂ Formalism.HermitianLatticesTheory.locS
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  rfl

/- English proof (translation)
The claim follows from `(algebraMap_smul D.host.E o v).symm`.
-/
theorem smul_eq_E (o : 𝓞 D.host.E) (v : (VS D).V) : o • v = (o : D.host.E) • v :=
  (algebraMap_smul D.host.E o v).symm

/- English proof (translation)
The claim follows from `(mem_LP P).mpr ⟨1, one_not_mem_P P, by rw [one_smul]; exact hx⟩`.
-/
theorem mem_localization_of_mem₃ {L : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} (hx : x ∈ L) : x ∈ LP P L :=
  (mem_LP P).mpr ⟨1, one_not_mem_P P, by rw [one_smul]; exact hx⟩

/- English proof (translation)
Take `⟨s, hs, h⟩` from `(mem_LP P).mp hx`. Conclude with `(mem_LP P).mpr ⟨s, hs, hle h⟩`.
-/
theorem localization_mono₃ {L L' : Submodule (𝓞 D.host.E) (VS D).V} (hle : L ≤ L') {x : (VS D).V} (hx : x ∈ LP P L) :
    x ∈ LP P L' := by
  obtain ⟨s, hs, h⟩ := (mem_LP P).mp hx
  exact (mem_LP P).mpr ⟨s, hs, hle h⟩

/- English proof (translation)
The claim follows from `add_mem hx hy`.
-/
theorem add_mem_localization {L : Submodule (𝓞 D.host.E) (VS D).V} {x y : (VS D).V} (hx : x ∈ LP P L) (hy : y ∈ LP P L) :
    x + y ∈ LP P L := add_mem hx hy

/- English proof (translation)
The claim follows from `sub_mem hx hy`.
-/
theorem sub_mem_localization {L : Submodule (𝓞 D.host.E) (VS D).V} {x y : (VS D).V} (hx : x ∈ LP P L) (hy : y ∈ LP P L) :
    x - y ∈ LP P L := sub_mem hx hy

/- English proof (translation)
Take `⟨s, hs, o, ho⟩` from `hc`. Take `⟨t, ht, h⟩` from `(mem_LP P).mp hx`. Use `(mem_LP P).mpr ⟨s * t, mul_not_mem_P P hs ht, ?_⟩` and prove the remaining obligations. Establish `: (s * t) • (c • x) = o • (t • x)`. Rewrite using `[smul_eq_E, smul_eq_E o, smul_eq_E t, smul_smul, smul_smul, ← ho]`.

Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[this]`. Conclude with `L.smul_mem o h`.
-/
theorem smul_mem_localization {L : Submodule (𝓞 D.host.E) (VS D).V} {c : D.host.E} (hc : IntP P c) {x : (VS D).V}
    (hx : x ∈ LP P L) : c • x ∈ LP P L := by
  obtain ⟨s, hs, o, ho⟩ := hc
  obtain ⟨t, ht, h⟩ := (mem_LP P).mp hx
  refine (mem_LP P).mpr ⟨s * t, mul_not_mem_P P hs ht, ?_⟩
  have : (s * t) • (c • x) = o • (t • x) := by
    rw [smul_eq_E, smul_eq_E o, smul_eq_E t, smul_smul, smul_smul, ← ho]
    push_cast
    ring_nf
  rw [this]
  exact L.smul_mem o h

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ h`.
-/
theorem LP_sum {L : Submodule (𝓞 D.host.E) (VS D).V} {ι : Type*} (s : Finset ι) (f : ι → (VS D).V)
    (h : ∀ i ∈ s, f i ∈ LP P L) : ∑ i ∈ s, f i ∈ LP P L := Submodule.sum_mem _ h

/- English proof (translation)
Take `⟨s, hs, h⟩` from `(mem_LP P).mp hx`. Use `(mem_LP P).mpr ⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_E, ← f.map_smul, ← smul_eq_E]`. Conclude with `hf _ h`.
-/
theorem LP_map {L L' : Submodule (𝓞 D.host.E) (VS D).V} (f : (VS D).V →ₗ[D.host.E] (VS D).V)
    (hf : ∀ v ∈ L, f v ∈ L') {x : (VS D).V} (hx : x ∈ LP P L) : f x ∈ LP P L' := by
  obtain ⟨s, hs, h⟩ := (mem_LP P).mp hx
  refine (mem_LP P).mpr ⟨s, hs, ?_⟩
  rw [smul_eq_E, ← f.map_smul, ← smul_eq_E]
  exact hf _ h

/- English proof (translation)
Establish `hc : (((g : ℕ) : 𝓞 D.host.E) : D.host.E) = ((g : ℕ) : D.host.E)` using `map_natCast (algebraMap (𝓞 D.host.E) D.host.E) g`. Rewrite using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, rfl⟩; exact ⟨l, hl, by rw [smul_eq_E, hc]⟩`. Introduce and unpack `⟨l, hl, rfl⟩; exact ⟨l, hl, by rw [smul_eq_E, hc]⟩`.
-/
theorem mem_gLam {Λ : Submodule (𝓞 D.host.E) (VS D).V} {g : ℕ} {x : (VS D).V} :
    x ∈ Ideal.span {((g : ℕ) : 𝓞 D.host.E)} • Λ ↔ ∃ l ∈ Λ, ((g : ℕ) : D.host.E) • l = x := by
  have hc : (((g : ℕ) : 𝓞 D.host.E) : D.host.E) = ((g : ℕ) : D.host.E) :=
    map_natCast (algebraMap (𝓞 D.host.E) D.host.E) g
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, by rw [smul_eq_E, hc]⟩
  · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, by rw [smul_eq_E, hc]⟩

/- English proof (translation)
Introduce `v hv`. Take `⟨l, hl, rfl⟩` from `mem_gLam.mp hv`. Conclude with `mem_gLam.mpr ⟨n l, nlam_mem hn hl, by simp⟩`.
-/
theorem nlam_gLam {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ G) (g : ℕ) :
    ∀ v ∈ Ideal.span {((g : ℕ) : 𝓞 D.host.E)} • Λ, (n : (VS D).V →ₗ[D.host.E] (VS D).V) v ∈
      Ideal.span {((g : ℕ) : 𝓞 D.host.E)} • Λ := by
  intro v hv
  obtain ⟨l, hl, rfl⟩ := mem_gLam.mp hv
  exact mem_gLam.mpr ⟨n l, nlam_mem hn hl, by simp⟩

end Loc

section Coef

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a', rfl⟩` from `hy`. Use `⟨e_mem_X F a', fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[coefX_e]`.

Use `split_ifs`. Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`. Consider the case `zero => exact ⟨zero_mem _, fun a => by rw [coefX_zero]; exact Subring.zero_mem _⟩`. Consider the case `add v w _ _ hv hw`.

Conclude with `⟨add_mem hv.1 hw.1, fun a => by rw [coefX_add _ hv.1 hw.1]; exact Subring.add_mem _ (hv.2 a) (hw.2 a)⟩`. Consider the case `smul o v _ hv`. Establish `e : o • v = (algebraMap (𝓞 E) E o) • v` using `(algebraMap_smul E o v).symm`. Use `⟨by rw [e]; exact Submodule.smul_mem _ _ hv.1, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[e, coefX_smul _ hv.1]`.

Conclude with `Subring.mul_mem _ ⟨o, rfl⟩ (hv.2 a)`.
-/
theorem coefX_of_mem_spanO (F : FlagG S r T) {u : S.V} (hu : u ∈ Submodule.span (𝓞 E) (Set.range F.e)) :
    u ∈ F.X ∧ ∀ a, F.coefX u a ∈ (algebraMap (𝓞 E) E).range := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a', rfl⟩ := hy
    refine ⟨e_mem_X F a', fun a => ?_⟩
    rw [coefX_e]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  | zero => exact ⟨zero_mem _, fun a => by rw [coefX_zero]; exact Subring.zero_mem _⟩
  | add v w _ _ hv hw =>
    exact ⟨add_mem hv.1 hw.1, fun a => by rw [coefX_add _ hv.1 hw.1]; exact Subring.add_mem _ (hv.2 a) (hw.2 a)⟩
  | smul o v _ hv =>
    have e : o • v = (algebraMap (𝓞 E) E o) • v := (algebraMap_smul E o v).symm
    refine ⟨by rw [e]; exact Submodule.smul_mem _ _ hv.1, fun a => ?_⟩
    rw [e, coefX_smul _ hv.1]
    exact Subring.mul_mem _ ⟨o, rfl⟩ (hv.2 a)

end Coef

section FixedConv

variable {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E))

/- English proof (translation)
Take `⟨c, _, hc1, hloc⟩` from `hC.1 P`. Establish `hc : (fun a => c a • G.fl.e a) = G.fl.e` using `funext fun a => by rw [hc1 hP a, one_smul]`. Rewrite `hloc` using `[hc]`. Conclude with `hloc`.
-/
theorem fixedConv_at {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    LP P (XLam Λ G) = LP P (Submodule.span (𝓞 D.host.E) (Set.range G.fl.e)) := by
  obtain ⟨c, _, hc1, hloc⟩ := hC.1 P
  have hc : (fun a => c a • G.fl.e a) = G.fl.e := funext fun a => by rw [hc1 hP a, one_smul]
  rw [hc] at hloc
  exact hloc

/- English proof (translation)
Establish `h : G.fl.e a ∈ LP P (Submodule.span (𝓞 D.host.E) (Set.range G.fl.e))` using `mem_localization_of_mem₃ P (Submodule.subset_span ⟨a, rfl⟩)`. Rewrite `h` using `[← fixedConv_at P hC hP]`. Conclude with `localization_mono₃ P (fun v hv => by rw [XLam, Submodule.mem_inf] at hv; exact hv.1) h`.
-/
theorem e_mem_LP {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (a : Fin D.R.rS) :
    G.fl.e a ∈ LP P Λ := by
  have h : G.fl.e a ∈ LP P (Submodule.span (𝓞 D.host.E) (Set.range G.fl.e)) :=
    mem_localization_of_mem₃ P (Submodule.subset_span ⟨a, rfl⟩)
  rw [← fixedConv_at P hC hP] at h
  exact localization_mono₃ P (fun v hv => by rw [XLam, Submodule.mem_inf] at hv; exact hv.1) h

/- English proof (translation)
Take `⟨s, hs, hsw⟩` from `(mem_LP P).mp hw`. Establish `hsX : s • w ∈ G.fl.X` using `by rw [smul_eq_E]; exact Submodule.smul_mem _ _ hwX`. Establish `h1 : s • w ∈ LP P (XLam Λ G)` using `mem_localization_of_mem₃ P (by rw [XLam, Submodule.mem_inf]; exact ⟨hsw, hsX⟩)`. Rewrite `h1` using `[fixedConv_at P hC hP]`. Take `⟨t, ht, h2⟩` from `(mem_LP P).mp h1`.

Take `⟨-, h3⟩` from `coefX_of_mem_spanO G.fl h2`. Take `⟨o, ho⟩` from `h3 a`. Use `⟨t * s, mul_not_mem_P P ht hs, o, ?_⟩` and prove the remaining obligations. Rewrite `ho` using `[smul_eq_E, smul_eq_E, coefX_smul _ (Submodule.smul_mem _ _ hwX), coefX_smul _ hwX]`. Establish `e2 : algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E)` using `rfl`.

Rewrite using `[← e2, ho]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_intP {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) {w : (VS D).V}
    (hw : w ∈ LP P Λ) (hwX : w ∈ G.fl.X) (a : Fin D.R.rS) : IntP P (G.fl.coefX w a) := by
  obtain ⟨s, hs, hsw⟩ := (mem_LP P).mp hw
  have hsX : s • w ∈ G.fl.X := by rw [smul_eq_E]; exact Submodule.smul_mem _ _ hwX
  have h1 : s • w ∈ LP P (XLam Λ G) := mem_localization_of_mem₃ P (by rw [XLam, Submodule.mem_inf]; exact ⟨hsw, hsX⟩)
  rw [fixedConv_at P hC hP] at h1
  obtain ⟨t, ht, h2⟩ := (mem_LP P).mp h1
  obtain ⟨-, h3⟩ := coefX_of_mem_spanO G.fl h2
  obtain ⟨o, ho⟩ := h3 a
  refine ⟨t * s, mul_not_mem_P P ht hs, o, ?_⟩
  rw [smul_eq_E, smul_eq_E, coefX_smul _ (Submodule.smul_mem _ _ hwX), coefX_smul _ hwX] at ho
  have e2 : algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) := rfl
  rw [← e2, ho]
  push_cast
  ring

/- English proof (translation)
Take `⟨s, hs, hsY⟩` from `(mem_LP P).mp hY`. Take `⟨l, hl, hlY⟩` from `mem_gLam.mp hsY`. Establish `hl' : l = ((s : D.host.E) / (gS D : D.host.E)) • Y`. Rewrite `hlY` using `[smul_eq_E]`. Rewrite using `[div_eq_mul_inv, mul_comm, ← smul_smul, ← hlY, smul_smul, inv_mul_cancel₀ hg, one_smul]`.

Establish `hlX : l ∈ G.fl.X` using `by rw [hl']; exact Submodule.smul_mem _ _ hYX`. Take `⟨t, ht, o, ho⟩` from `coef_intP P hC hP (mem_localization_of_mem₃ P hl) hlX a`. Use `⟨t * s, mul_not_mem_P P ht hs, o, ?_⟩` and prove the remaining obligations. Rewrite `ho` using `[hl', coefX_smul _ hYX]`. Rewrite using `[← ho]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_intP_g {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {G : LFlag (VS D) D.R.rS T}
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (hg : ((gS D : ℕ) : D.host.E) ≠ 0) {Y : (VS D).V}
    (hY : Y ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ)) (hYX : Y ∈ G.fl.X) (a : Fin D.R.rS) :
    IntP P (G.fl.coefX Y a / (gS D : D.host.E)) := by
  obtain ⟨s, hs, hsY⟩ := (mem_LP P).mp hY
  obtain ⟨l, hl, hlY⟩ := mem_gLam.mp hsY
  have hl' : l = ((s : D.host.E) / (gS D : D.host.E)) • Y := by
    rw [smul_eq_E] at hlY
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← hlY, smul_smul, inv_mul_cancel₀ hg, one_smul]
  have hlX : l ∈ G.fl.X := by rw [hl']; exact Submodule.smul_mem _ _ hYX
  obtain ⟨t, ht, o, ho⟩ := coef_intP P hC hP (mem_localization_of_mem₃ P hl) hlX a
  refine ⟨t * s, mul_not_mem_P P ht hs, o, ?_⟩
  rw [hl', coefX_smul _ hYX] at ho
  rw [← ho]
  push_cast
  ring

end FixedConv

end PI.NRCW
