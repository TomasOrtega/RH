import Mathlib
import GroundTheory.GlobalFields.HerbrandQuotients.Cyclic
import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply
import GroundTheory.GlobalFields.SemilocalAlgebras.Infinite

noncomputable section

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.ProfCoh
  GroundTheory.GroupCoh
open scoped NumberField.LiesOver ComplexConjugate

/- English proof (translation)
Establish `: Subsingleton (KerModRange f g)` using `⟨fun p q => by`. Proceed by induction on `p using QuotientAddGroup.induction_on with | H x =>`. Proceed by induction on `q using QuotientAddGroup.induction_on with | H y =>`. Rewrite using `[KerModRange.mk_eq_mk_iff]`. Conclude with `h _ (sub_mem x.2 y.2)⟩`.

Conclude with `Nat.card_of_subsingleton (0 : KerModRange f g)`.
-/
theorem natCard_kerModRange_eq_one {A : Type*} [AddCommGroup A] {f g : A →+ A}
    (h : ∀ x ∈ f.ker, x ∈ g.range) : Nat.card (KerModRange f g) = 1 := by
  have : Subsingleton (KerModRange f g) := ⟨fun p q => by
    induction p using QuotientAddGroup.induction_on with | H x =>
    induction q using QuotientAddGroup.induction_on with | H y =>
    rw [KerModRange.mk_eq_mk_iff]
    exact h _ (sub_mem x.2 y.2)⟩
  exact Nat.card_of_subsingleton (0 : KerModRange f g)

namespace InfinitePlace

def realSignHom {G : Type*} [Group G] (c : G) (hc : c * c = 1) : ℝˣ →* G where
  toFun x := if (x : ℝ) < 0 then c else 1
  map_one' := by simp
  map_mul' x y := by
    simp only [Units.val_mul]
    rcases lt_or_gt_of_ne x.ne_zero with hx | hx <;>
      rcases lt_or_gt_of_ne y.ne_zero with hy | hy
    · simp [hx, hy, not_lt.2 (mul_pos_of_neg_of_neg hx hy).le, hc]
    · simp [hx, not_lt.2 hy.le, mul_neg_of_neg_of_pos hx hy]
    · simp [not_lt.2 hx.le, hy, mul_neg_of_pos_of_neg hx hy]
    · simp [not_lt.2 hx.le, not_lt.2 hy.le, not_lt.2 (mul_pos hx hy).le]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem realSignHom_apply {G : Type*} [Group G] (c : G) (hc : c * c = 1) (x : ℝˣ) :
    realSignHom c hc x = if (x : ℝ) < 0 then c else 1 :=
  rfl

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K}
  (w : InfinitePlace L) [w.LiesOver v]

section Degree

/- English proof (translation)
Establish `hc : w.comap (algebraMap K L) = v` using `NumberField.InfinitePlace.LiesOver.comap_eq w v`. Break down `w.isUnramified_or_isRamified K with h | h` into its components or cases. Rewrite using `[h.finrank_eq_one v]`. Use `⟨fun h' => absurd h' (by norm_num), fun ⟨hv, hw⟩ => absurd h ?_⟩` and prove the remaining obligations. Conclude with `isRamified_iff.2 ⟨hw, hc ▸ hv⟩`.

Rewrite using `[h.finrank_eq_two v]`. Conclude with `⟨fun _ => ⟨hc ▸ h.isReal, h.isComplex⟩, fun _ => rfl⟩`.
-/
theorem finrank_completion_eq_two_iff :
    Module.finrank v.Completion w.Completion = 2 ↔ v.IsReal ∧ w.IsComplex := by
  have hc : w.comap (algebraMap K L) = v := NumberField.InfinitePlace.LiesOver.comap_eq w v
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v]
    refine ⟨fun h' => absurd h' (by norm_num), fun ⟨hv, hw⟩ => absurd h ?_⟩
    exact isRamified_iff.2 ⟨hw, hc ▸ hv⟩
  · rw [h.finrank_eq_two v]
    exact ⟨fun _ => ⟨hc ▸ h.isReal, h.isComplex⟩, fun _ => rfl⟩

/- English proof (translation)
Rewrite using `[← finrank_completion_eq_two_iff w]`. Break down `w.isUnramified_or_isRamified K with h | h` into its components or cases. Rewrite using `[h.finrank_eq_one v]`. Evaluate the numerical expressions. Rewrite using `[h.finrank_eq_two v]`.

Evaluate the numerical expressions.
-/
theorem finrank_completion_eq_one_iff :
    Module.finrank v.Completion w.Completion = 1 ↔ ¬ (v.IsReal ∧ w.IsComplex) := by
  rw [← finrank_completion_eq_two_iff w]
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v]; norm_num
  · rw [h.finrank_eq_two v]; norm_num

end Degree

section Conj

variable {w}

/- English proof (translation)
Use `NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv` as an intermediate fact. Rewrite using `[extensionEmbeddingOfIsReal_apply]`. Conclude with `Completion.liesOver_extensionEmbedding_apply w v`.
-/
theorem extensionEmbedding_algebraMap (hv : v.IsReal) (x : v.Completion) :
    extensionEmbedding w (algebraMap v.Completion w.Completion x) =
      (extensionEmbeddingOfIsReal hv x : ℂ) := by
  have := NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv
  rw [extensionEmbeddingOfIsReal_apply]
  exact Completion.liesOver_extensionEmbedding_apply w v

open scoped Classical in

def completionConj (hv : v.IsReal) : Gal(w.Completion/v.Completion) :=
  if hw : w.IsComplex then
    AlgEquiv.ofRingEquiv (f := ((ringEquivComplexOfIsComplex hw).trans
      (starRingAut : RingAut ℂ)).trans (ringEquivComplexOfIsComplex hw).symm) (fun x => by
        apply (ringEquivComplexOfIsComplex hw).injective
        simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply, ringEquivComplexOfIsComplex_apply,
          extensionEmbedding_algebraMap hv, starRingAut_apply]
        exact Complex.conj_ofReal _)
  else 1

/- English proof (translation)
Distinguish the cases in `hw : w.IsComplex`. Rewrite using `[← ringEquivComplexOfIsComplex_apply hw]`. Simplify using `[completionConj, dif_pos hw]`. Rewrite using `[completionConj, dif_neg hw, AlgEquiv.one_apply, ← extensionEmbeddingOfIsReal_apply (not_isComplex_iff_isReal.1 hw), Complex.conj_ofReal]`.
-/
theorem extensionEmbedding_completionConj (hv : v.IsReal) (x : w.Completion) :
    extensionEmbedding w (completionConj hv x) = conj (extensionEmbedding w x) := by
  by_cases hw : w.IsComplex
  · rw [← ringEquivComplexOfIsComplex_apply hw]
    simp [completionConj, dif_pos hw]
  · rw [completionConj, dif_neg hw, AlgEquiv.one_apply,
      ← extensionEmbeddingOfIsReal_apply (not_isComplex_iff_isReal.1 hw), Complex.conj_ofReal]

/- English proof (translation)
Use `AlgEquiv.ext fun x => ?_` and prove the remaining obligations. Apply `(extensionEmbedding w).injective` to reduce the goal to its premises. Simplify using `[AlgEquiv.mul_apply, extensionEmbedding_completionConj]`.
-/
theorem completionConj_mul_self (hv : v.IsReal) :
    completionConj (w := w) hv * completionConj hv = 1 := by
  refine AlgEquiv.ext fun x => ?_
  apply (extensionEmbedding w).injective
  simp [AlgEquiv.mul_apply, extensionEmbedding_completionConj]

/- English proof (translation)
Introduce `h`. Take `⟨z, hz⟩` from `surjective_extensionEmbedding_of_isComplex hw Complex.I`. Use `extensionEmbedding_completionConj (w := w) hv z` as an intermediate fact. Rewrite `this` using `[h, AlgEquiv.one_apply, hz, Complex.conj_I]`. Establish `h2 : (2 : ℂ) * Complex.I = 0` using `by linear_combination this`.

Simplify using `at h2`.
-/
theorem completionConj_ne_one (hv : v.IsReal) (hw : w.IsComplex) :
    completionConj (w := w) hv ≠ 1 := by
  intro h
  obtain ⟨z, hz⟩ := surjective_extensionEmbedding_of_isComplex hw Complex.I
  have := extensionEmbedding_completionConj (w := w) hv z
  rw [h, AlgEquiv.one_apply, hz, Complex.conj_I] at this
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination this
  simp at h2

open scoped Classical in

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `hcard` using `AlgEquiv.card_le (F := v.Completion) (K := w.Completion)`. Rewrite `hcard` using `[(finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩]`. Establish `h3 : ({1, completionConj hv, σ} : Finset Gal(w.Completion/v.Completion)).card = 3` using `Finset.card_eq_three.2 ⟨1, completionConj hv, σ, (completionConj_ne_one hv hw).symm, h.1.symm, h.2.symm, rfl⟩`.

Use `Finset.card_le_univ ({1, completionConj hv, σ} : Finset Gal(w.Completion/v.Completion))` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_one_or_eq_completionConj (hv : v.IsReal) (hw : w.IsComplex)
    (σ : Gal(w.Completion/v.Completion)) : σ = 1 ∨ σ = completionConj hv := by
  by_contra h
  push Not at h
  have hcard := AlgEquiv.card_le (F := v.Completion) (K := w.Completion)
  rw [(finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩] at hcard
  have h3 : ({1, completionConj hv, σ} : Finset Gal(w.Completion/v.Completion)).card = 3 :=
    Finset.card_eq_three.2 ⟨1, completionConj hv, σ, (completionConj_ne_one hv hw).symm,
      h.1.symm, h.2.symm, rfl⟩
  have := Finset.card_le_univ ({1, completionConj hv, σ} : Finset Gal(w.Completion/v.Completion))
  omega

open scoped Classical in

/- English proof (translation)
Use extensionality with `σ`. Simplify using `only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]`. Conclude with `eq_one_or_eq_completionConj hv hw σ`.
-/
theorem univ_eq_one_completionConj (hv : v.IsReal) (hw : w.IsComplex) :
    (Finset.univ : Finset Gal(w.Completion/v.Completion)) = {1, completionConj hv} := by
  ext σ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact eq_one_or_eq_completionConj hv hw σ

/- English proof (translation)
Rewrite using `[← Finset.card_univ, univ_eq_one_completionConj hv hw]`. Conclude with `Finset.card_pair (completionConj_ne_one hv hw).symm`.
-/
theorem card_gal_eq_two (hv : v.IsReal) (hw : w.IsComplex) :
    Fintype.card Gal(w.Completion/v.Completion) = 2 := by
  classical
  rw [← Finset.card_univ, univ_eq_one_completionConj hv hw]
  exact Finset.card_pair (completionConj_ne_one hv hw).symm

variable (w) in

/- English proof (translation)
Establish `hcard` using `AlgEquiv.card_le (F := v.Completion) (K := w.Completion)`. Rewrite `hcard` using `[(finrank_completion_eq_one_iff w).2 h]`. Conclude with `Fintype.card_le_one_iff_subsingleton.1 hcard`.
-/
theorem subsingleton_gal (h : ¬ (v.IsReal ∧ w.IsComplex)) :
    Subsingleton Gal(w.Completion/v.Completion) := by
  have hcard := AlgEquiv.card_le (F := v.Completion) (K := w.Completion)
  rw [(finrank_completion_eq_one_iff w).2 h] at hcard
  exact Fintype.card_le_one_iff_subsingleton.1 hcard

variable (w) in

/- English proof (translation)
Rewrite using `[Nat.card_eq_fintype_card]`. Distinguish the cases in `h2 : v.IsReal ∧ w.IsComplex`. Rewrite using `[card_gal_eq_two h2.1 h2.2, (finrank_completion_eq_two_iff w).2 h2]`. Rewrite using `[(finrank_completion_eq_one_iff w).2 h2]`. Use `subsingleton_gal w h2` as an intermediate fact.

Conclude with `Fintype.card_eq_one_iff.2 ⟨1, fun _ => Subsingleton.elim _ _⟩`.
-/
theorem natCard_gal_completion :
    Nat.card Gal(w.Completion/v.Completion) = Module.finrank v.Completion w.Completion := by
  rw [Nat.card_eq_fintype_card]
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · rw [card_gal_eq_two h2.1 h2.2, (finrank_completion_eq_two_iff w).2 h2]
  · rw [(finrank_completion_eq_one_iff w).2 h2]
    have := subsingleton_gal w h2
    exact Fintype.card_eq_one_iff.2 ⟨1, fun _ => Subsingleton.elim _ _⟩

instance isGalois_completion : IsGalois v.Completion w.Completion :=
  IsGalois.of_card_aut_eq_finrank (h := natCard_gal_completion w)

end Conj

section Norm

variable {w}

/- English proof (translation)
Rewrite using `[Algebra.norm_eq_prod_automorphisms, univ_eq_one_completionConj hv hw, Finset.prod_pair (completionConj_ne_one hv hw).symm, AlgEquiv.one_apply]`.
-/
theorem algebraMap_norm_completion (hv : v.IsReal) (hw : w.IsComplex) (y : w.Completion) :
    algebraMap v.Completion w.Completion (Algebra.norm v.Completion y) =
      y * completionConj (w := w) hv y := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, univ_eq_one_completionConj hv hw,
    Finset.prod_pair (completionConj_ne_one hv hw).symm, AlgEquiv.one_apply]

/- English proof (translation)
Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[← extensionEmbedding_algebraMap (w := w) hv, algebraMap_norm_completion hv hw, map_mul, extensionEmbedding_completionConj, Complex.mul_conj]`.
-/
theorem extensionEmbeddingOfIsReal_norm (hv : v.IsReal) (hw : w.IsComplex) (y : w.Completion) :
    extensionEmbeddingOfIsReal hv (Algebra.norm v.Completion y) =
      Complex.normSq (extensionEmbedding w y) := by
  apply Complex.ofReal_injective
  rw [← extensionEmbedding_algebraMap (w := w) hv, algebraMap_norm_completion hv hw, map_mul,
    extensionEmbedding_completionConj, Complex.mul_conj]

variable (v w) in

def normSubgroup : Subgroup v.Completionˣ :=
  (Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion)).range

/- English proof (translation)
Rewrite using `[normSubgroup, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Rewrite using `[Units.coe_map, extensionEmbeddingOfIsReal_norm hv hw]`. Conclude with `Complex.normSq_pos.2 ((map_ne_zero _).2 y.ne_zero)`.

Introduce `hx`. Take `⟨a, ha⟩` from `surjective_extensionEmbeddingOfIsReal hv (Real.sqrt (extensionEmbeddingOfIsReal hv x))`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `ha` using `[map_zero, eq_comm, Real.sqrt_eq_zero hx.le]`.

Conclude with `hx.ne' ha`. Use `⟨Units.mk0 (algebraMap v.Completion w.Completion a) ((map_ne_zero _).2 ha0), ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.coe_map, Units.val_mk0, Algebra.norm_algebraMap, (finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩]`. Apply `(extensionEmbeddingOfIsReal hv).injective` to reduce the goal to its premises.

Rewrite using `[map_pow, ha, Real.sq_sqrt hx.le]`.
-/
theorem mem_normSubgroup_iff (hv : v.IsReal) (hw : w.IsComplex) (x : v.Completionˣ) :
    x ∈ normSubgroup v w ↔ 0 < extensionEmbeddingOfIsReal hv x := by
  rw [normSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rw [Units.coe_map, extensionEmbeddingOfIsReal_norm hv hw]
    exact Complex.normSq_pos.2 ((map_ne_zero _).2 y.ne_zero)
  · intro hx
    obtain ⟨a, ha⟩ := surjective_extensionEmbeddingOfIsReal hv
      (Real.sqrt (extensionEmbeddingOfIsReal hv x))
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero, eq_comm, Real.sqrt_eq_zero hx.le] at ha
      exact hx.ne' ha
    refine ⟨Units.mk0 (algebraMap v.Completion w.Completion a) ((map_ne_zero _).2 ha0), ?_⟩
    apply Units.ext
    rw [Units.coe_map, Units.val_mk0, Algebra.norm_algebraMap,
      (finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩]
    apply (extensionEmbeddingOfIsReal hv).injective
    rw [map_pow, ha, Real.sq_sqrt hx.le]

variable (w) in

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Use `⟨Units.map (algebraMap v.Completion w.Completion : v.Completion →* w.Completion) x, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.coe_map, Units.coe_map, MonoidHom.coe_coe, Algebra.norm_algebraMap, (finrank_completion_eq_one_iff w).2 h, pow_one]`.
-/
theorem normSubgroup_eq_top (h : ¬ (v.IsReal ∧ w.IsComplex)) : normSubgroup v w = ⊤ := by
  rw [eq_top_iff]
  intro x _
  refine ⟨Units.map (algebraMap v.Completion w.Completion : v.Completion →* w.Completion) x, ?_⟩
  apply Units.ext
  rw [Units.coe_map, Units.coe_map, MonoidHom.coe_coe, Algebra.norm_algebraMap,
    (finrank_completion_eq_one_iff w).2 h, pow_one]

end Norm

section LocalSymbol

variable (v)

open scoped Classical in

def localSymbol : v.Completionˣ →* Gal(w.Completion/v.Completion) :=
  if hv : v.IsReal then
    (realSignHom (completionConj (w := w) hv) (completionConj_mul_self hv)).comp
      (Units.map (extensionEmbeddingOfIsReal hv).toMonoidHom)
  else 1

/- English proof (translation)
Simplify using `only [localSymbol, dif_pos hv, MonoidHom.comp_apply, realSignHom_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]`. Conclude with `if_congr Iff.rfl rfl rfl`.
-/
theorem localSymbol_apply (hv : v.IsReal) (x : v.Completionˣ) :
    localSymbol v w x =
      if extensionEmbeddingOfIsReal hv x < 0 then completionConj hv else 1 := by
  simp only [localSymbol, dif_pos hv, MonoidHom.comp_apply, realSignHom_apply, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact if_congr Iff.rfl rfl rfl

/- English proof (translation)
Rewrite using `[localSymbol, dif_neg hv]`.
-/
theorem localSymbol_of_not_isReal (hv : ¬ v.IsReal) : localSymbol v w = 1 := by
  rw [localSymbol, dif_neg hv]

/- English proof (translation)
Distinguish the cases in `h2 : v.IsReal ∧ w.IsComplex`. Take `⟨hv, hw⟩` from `h2`. Use extensionality with `x`. Rewrite using `[MonoidHom.mem_ker, localSymbol_apply v w hv, mem_normSubgroup_iff hv hw]`. Establish `hx0 : extensionEmbeddingOfIsReal hv x ≠ 0` using `(map_ne_zero _).2 x.ne_zero`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hneg`. Establish `hlt : extensionEmbeddingOfIsReal hv x < 0` using `lt_of_le_of_ne (not_lt.1 hneg) hx0`. Rewrite `h` using `[if_pos hlt]`.

Conclude with `completionConj_ne_one hv hw h`. Introduce `h`. Rewrite using `[if_neg (not_lt.2 h.le)]`. Rewrite using `[normSubgroup_eq_top w h2, eq_top_iff]`. Introduce `x _`.

Rewrite using `[MonoidHom.mem_ker]`. Distinguish the cases in `hv : v.IsReal`. Establish `hw : ¬ w.IsComplex` using `fun hw => h2 ⟨hv, hw⟩`. Rewrite using `[localSymbol_apply v w hv, completionConj, dif_neg hw, ite_self]`. Rewrite using `[localSymbol_of_not_isReal v w hv, MonoidHom.one_apply]`.
-/
theorem ker_localSymbol : (localSymbol v w).ker = normSubgroup v w := by
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · obtain ⟨hv, hw⟩ := h2
    ext x
    rw [MonoidHom.mem_ker, localSymbol_apply v w hv, mem_normSubgroup_iff hv hw]
    have hx0 : extensionEmbeddingOfIsReal hv x ≠ 0 := (map_ne_zero _).2 x.ne_zero
    constructor
    · intro h
      by_contra hneg
      have hlt : extensionEmbeddingOfIsReal hv x < 0 := lt_of_le_of_ne (not_lt.1 hneg) hx0
      rw [if_pos hlt] at h
      exact completionConj_ne_one hv hw h
    · intro h
      rw [if_neg (not_lt.2 h.le)]
  · rw [normSubgroup_eq_top w h2, eq_top_iff]
    intro x _
    rw [MonoidHom.mem_ker]
    by_cases hv : v.IsReal
    · have hw : ¬ w.IsComplex := fun hw => h2 ⟨hv, hw⟩
      rw [localSymbol_apply v w hv, completionConj, dif_neg hw, ite_self]
    · rw [localSymbol_of_not_isReal v w hv, MonoidHom.one_apply]

/- English proof (translation)
Introduce `σ`. Distinguish the cases in `h2 : v.IsReal ∧ w.IsComplex`. Take `⟨hv, hw⟩` from `h2`. Break down `eq_one_or_eq_completionConj hv hw σ with rfl | rfl` into its components or cases. Conclude with `⟨1, map_one _⟩`.

Use `⟨-1, ?_⟩` and prove the remaining obligations. Rewrite using `[localSymbol_apply v w hv, if_pos]`. Simplify using the standard rewrite rules. Use `subsingleton_gal w h2` as an intermediate fact. Conclude with `⟨1, Subsingleton.elim _ _⟩`.
-/
theorem localSymbol_surjective : Function.Surjective (localSymbol v w) := by
  intro σ
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · obtain ⟨hv, hw⟩ := h2
    rcases eq_one_or_eq_completionConj hv hw σ with rfl | rfl
    · exact ⟨1, map_one _⟩
    · refine ⟨-1, ?_⟩
      rw [localSymbol_apply v w hv, if_pos]
      simp
  · have := subsingleton_gal w h2
    exact ⟨1, Subsingleton.elim _ _⟩

def normQuotientEquivGal : v.Completionˣ ⧸ normSubgroup v w ≃* Gal(w.Completion/v.Completion) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_localSymbol v w).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (localSymbol_surjective v w))

/- English proof (translation)
Rewrite using `[Nat.card_congr (normQuotientEquivGal v w).toEquiv, natCard_gal_completion w]`.
-/
theorem natCard_quotient_normSubgroup :
    Nat.card (v.Completionˣ ⧸ normSubgroup v w) = Module.finrank v.Completion w.Completion := by
  rw [Nat.card_congr (normQuotientEquivGal v w).toEquiv, natCard_gal_completion w]

end LocalSymbol

section Herbrand

variable (v)

abbrev unitsRep : Representation ℤ Gal(w.Completion/v.Completion) (Additive w.Completionˣ) :=
  zRepOfMonoidEnd (galUnitsHom v.Completion w.Completion)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unitsRep_toMul (σ : Gal(w.Completion/v.Completion)) (x : Additive w.Completionˣ) :
    ((unitsRep v w σ x).toMul : w.Completion) = σ (x.toMul : w.Completion) :=
  rfl

/- English proof (translation)
Rewrite using `[cycSub_apply, toMul_sub, Units.val_div_eq_div_val, unitsRep_toMul]`.
-/
theorem cycSub_unitsRep_toMul (σ : Gal(w.Completion/v.Completion)) (x : Additive w.Completionˣ) :
    ((cycSub (unitsRep v w) σ x).toMul : w.Completion) =
      σ (x.toMul : w.Completion) / (x.toMul : w.Completion) := by
  rw [cycSub_apply, toMul_sub, Units.val_div_eq_div_val, unitsRep_toMul]

variable {v w}

/- English proof (translation)
Rewrite using `[normHom_apply, univ_eq_one_completionConj hv hw, Finset.sum_pair (completionConj_ne_one hv hw).symm, toMul_add, Units.val_mul, unitsRep_toMul, unitsRep_toMul, AlgEquiv.one_apply]`.
-/
theorem normHom_unitsRep_toMul (hv : v.IsReal) (hw : w.IsComplex) (x : Additive w.Completionˣ) :
    ((normHom (unitsRep v w) x).toMul : w.Completion) =
      (x.toMul : w.Completion) * completionConj (w := w) hv (x.toMul : w.Completion) := by
  classical
  rw [normHom_apply, univ_eq_one_completionConj hv hw,
    Finset.sum_pair (completionConj_ne_one hv hw).symm, toMul_add, Units.val_mul, unitsRep_toMul,
    unitsRep_toMul, AlgEquiv.one_apply]

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Rewrite using `[normHom_unitsRep_toMul hv hw, map_mul, extensionEmbedding_completionConj, Complex.mul_conj, Complex.ofReal_re]`. Conclude with `Complex.normSq_pos.2 ((map_ne_zero _).2 (Units.ne_zero _))`.
-/
theorem re_pos_of_mem_range_normHom (hv : v.IsReal) (hw : w.IsComplex)
    {x : Additive w.Completionˣ} (hx : x ∈ (normHom (unitsRep v w)).range) :
    0 < (extensionEmbedding w (x.toMul : w.Completion)).re := by
  obtain ⟨y, rfl⟩ := hx
  rw [normHom_unitsRep_toMul hv hw, map_mul, extensionEmbedding_completionConj, Complex.mul_conj,
    Complex.ofReal_re]
  exact Complex.normSq_pos.2 ((map_ne_zero _).2 (Units.ne_zero _))

/- English proof (translation)
Establish `hreal : extensionEmbedding w (x.toMul : w.Completion) = ((extensionEmbedding w (x.toMul : w.Completion)).re : ℂ)`. Establish `h` using `extensionEmbedding_completionConj (w := w) hv (x.toMul : w.Completion)`. Rewrite `h` using `[hx]`. Conclude with `(Complex.conj_eq_iff_re.1 h.symm).symm`. Use `set r := (extensionEmbedding w (x.toMul : w.Completion)).re`.

Take `⟨a, ha⟩` from `surjective_extensionEmbedding_of_isComplex hw (Real.sqrt r : ℂ)`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `ha` using `[map_zero, eq_comm, Complex.ofReal_eq_zero, Real.sqrt_eq_zero hpos.le]`. Conclude with `hpos.ne' ha`.

Use `⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩` and prove the remaining obligations. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Apply `(extensionEmbedding w).injective` to reduce the goal to its premises. Rewrite using `[normHom_unitsRep_toMul hv hw, toMul_ofMul, Units.val_mk0, map_mul, extensionEmbedding_completionConj, ha, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le, ← hreal]`.
-/
theorem mem_range_normHom (hv : v.IsReal) (hw : w.IsComplex) (x : Additive w.Completionˣ)
    (hx : completionConj (w := w) hv (x.toMul : w.Completion) = x.toMul)
    (hpos : 0 < (extensionEmbedding w (x.toMul : w.Completion)).re) :
    x ∈ (normHom (unitsRep v w)).range := by
  have hreal : extensionEmbedding w (x.toMul : w.Completion) =
      ((extensionEmbedding w (x.toMul : w.Completion)).re : ℂ) := by
    have h := extensionEmbedding_completionConj (w := w) hv (x.toMul : w.Completion)
    rw [hx] at h
    exact (Complex.conj_eq_iff_re.1 h.symm).symm
  set r := (extensionEmbedding w (x.toMul : w.Completion)).re
  obtain ⟨a, ha⟩ := surjective_extensionEmbedding_of_isComplex hw (Real.sqrt r : ℂ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Complex.ofReal_eq_zero, Real.sqrt_eq_zero hpos.le] at ha
    exact hpos.ne' ha
  refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  apply (extensionEmbedding w).injective
  rw [normHom_unitsRep_toMul hv hw, toMul_ofMul, Units.val_mk0, map_mul,
    extensionEmbedding_completionConj, ha, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hpos.le, ← hreal]

/- English proof (translation)
Distinguish the cases in `h : 1 + conj z = 0`. Use `⟨Complex.I, Complex.I_ne_zero, ?_⟩` and prove the remaining obligations. Establish `h1 : conj z = -1` using `by linear_combination h`. Establish `h2 : z = -1` using `by simpa using congrArg conj h1`. Rewrite using `[h2, Complex.conj_I]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨1 + conj z, h, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_one, Complex.conj_conj]`. Take the linear combination `-hz`.
-/
theorem exists_conj_eq_mul {z : ℂ} (hz : z * conj z = 1) : ∃ u : ℂ, u ≠ 0 ∧ conj u = z * u := by
  by_cases h : 1 + conj z = 0
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    have h1 : conj z = -1 := by linear_combination h
    have h2 : z = -1 := by simpa using congrArg conj h1
    rw [h2, Complex.conj_I]
    ring
  · refine ⟨1 + conj z, h, ?_⟩
    rw [map_add, map_one, Complex.conj_conj]
    linear_combination -hz

variable (v w)

/- English proof (translation)
Use `set c := completionConj (w := w) hv`. Establish `hker : ∀ x : Additive w.Completionˣ, x ∈ (cycSub (unitsRep v w) c).ker ↔ c (x.toMul : w.Completion) = x.toMul`. Introduce `x`. Rewrite using `[AddMonoidHom.mem_ker, ← toMul_eq_one, ← Units.val_eq_one, cycSub_unitsRep_toMul, div_eq_one_iff_eq (Units.ne_zero _)]`. Use `set m : Additive w.Completionˣ := Additive.ofMul (-1)`.

Establish `hm : m ∈ (cycSub (unitsRep v w) c).ker`. Rewrite using `[hker]`. Simplify using `[m]`. Establish `hme : extensionEmbedding w (m.toMul : w.Completion) = -1` using `by simp [m]`. Rewrite using `[Nat.card_eq_two_iff]`.

Use `⟨QuotientAddGroup.mk ⟨0, zero_mem _⟩, QuotientAddGroup.mk ⟨m, hm⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, KerModRange.mk_eq_mk_iff]`. Introduce `h`. Use `re_pos_of_mem_range_normHom hv hw h` as an intermediate fact. Rewrite `this` using `[AddSubgroup.coe_mk, zero_sub, toMul_neg, Units.val_inv_eq_inv_val, map_inv₀, hme]`.

Evaluate the numerical expressions using `at this`. Rewrite using `[Set.eq_univ_iff_forall]`. Introduce `q`. Proceed by induction on `q using QuotientAddGroup.induction_on with | H z =>`. Take `⟨x, hx⟩` from `z`.

Establish `hc` using `(hker x).1 hx`. Establish `hreal : extensionEmbedding w (x.toMul : w.Completion) = ((extensionEmbedding w (x.toMul : w.Completion)).re : ℂ)`. Establish `h` using `extensionEmbedding_completionConj (w := w) hv (x.toMul : w.Completion)`. Rewrite `h` using `[hc]`. Conclude with `(Complex.conj_eq_iff_re.1 h.symm).symm`.

Establish `hne : (extensionEmbedding w (x.toMul : w.Completion)).re ≠ 0`. Introduce `h0`. Rewrite `hreal` using `[h0, Complex.ofReal_zero, map_eq_zero]`. Conclude with `Units.ne_zero _ hreal`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff]`.

Break down `lt_or_gt_of_ne hne with hneg | hpos` into its components or cases. Use `right`. Rewrite using `[KerModRange.mk_eq_mk_iff]`. Apply `mem_range_normHom hv hw` to reduce the goal to its premises. Rewrite using `[AddSubgroup.coe_mk, AddSubgroup.coe_mk, toMul_sub, Units.val_div_eq_div_val, map_div₀, hc, (hker m).1 hm]`.

Rewrite using `[AddSubgroup.coe_mk, AddSubgroup.coe_mk, toMul_sub, Units.val_div_eq_div_val, map_div₀, hme, div_neg, div_one, Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `left`. Rewrite using `[KerModRange.mk_eq_mk_iff, AddSubgroup.coe_mk, AddSubgroup.coe_mk, sub_zero]`. Conclude with `mem_range_normHom hv hw x hc hpos`.
-/
theorem natCard_kerModRange_cycSub_normHom (hv : v.IsReal) (hw : w.IsComplex) :
    Nat.card (KerModRange (cycSub (unitsRep v w) (completionConj hv))
      (normHom (unitsRep v w))) = 2 := by
  set c := completionConj (w := w) hv
  have hker : ∀ x : Additive w.Completionˣ,
      x ∈ (cycSub (unitsRep v w) c).ker ↔ c (x.toMul : w.Completion) = x.toMul := by
    intro x
    rw [AddMonoidHom.mem_ker, ← toMul_eq_one, ← Units.val_eq_one, cycSub_unitsRep_toMul,
      div_eq_one_iff_eq (Units.ne_zero _)]
  set m : Additive w.Completionˣ := Additive.ofMul (-1)
  have hm : m ∈ (cycSub (unitsRep v w) c).ker := by
    rw [hker]
    simp [m]
  have hme : extensionEmbedding w (m.toMul : w.Completion) = -1 := by simp [m]
  rw [Nat.card_eq_two_iff]
  refine ⟨QuotientAddGroup.mk ⟨0, zero_mem _⟩, QuotientAddGroup.mk ⟨m, hm⟩, ?_, ?_⟩
  · rw [Ne, KerModRange.mk_eq_mk_iff]
    intro h
    have := re_pos_of_mem_range_normHom hv hw h
    rw [AddSubgroup.coe_mk, zero_sub, toMul_neg, Units.val_inv_eq_inv_val, map_inv₀, hme] at this
    norm_num at this
  · rw [Set.eq_univ_iff_forall]
    intro q
    induction q using QuotientAddGroup.induction_on with | H z =>
    obtain ⟨x, hx⟩ := z
    have hc := (hker x).1 hx
    have hreal : extensionEmbedding w (x.toMul : w.Completion) =
        ((extensionEmbedding w (x.toMul : w.Completion)).re : ℂ) := by
      have h := extensionEmbedding_completionConj (w := w) hv (x.toMul : w.Completion)
      rw [hc] at h
      exact (Complex.conj_eq_iff_re.1 h.symm).symm
    have hne : (extensionEmbedding w (x.toMul : w.Completion)).re ≠ 0 := by
      intro h0
      rw [h0, Complex.ofReal_zero, map_eq_zero] at hreal
      exact Units.ne_zero _ hreal
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · right
      rw [KerModRange.mk_eq_mk_iff]
      apply mem_range_normHom hv hw
      · rw [AddSubgroup.coe_mk, AddSubgroup.coe_mk, toMul_sub, Units.val_div_eq_div_val, map_div₀, hc,
          (hker m).1 hm]
      · rw [AddSubgroup.coe_mk, AddSubgroup.coe_mk, toMul_sub, Units.val_div_eq_div_val, map_div₀,
          hme, div_neg, div_one, Complex.neg_re]
        linarith
    · left
      rw [KerModRange.mk_eq_mk_iff, AddSubgroup.coe_mk, AddSubgroup.coe_mk, sub_zero]
      exact mem_range_normHom hv hw x hc hpos

/- English proof (translation)
Apply `natCard_kerModRange_eq_one` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[AddMonoidHom.mem_ker, ← toMul_eq_one, ← Units.val_eq_one, normHom_unitsRep_toMul hv hw]`. Establish `hz : extensionEmbedding w (x.toMul : w.Completion) * conj (extensionEmbedding w (x.toMul : w.Completion)) = 1`. Rewrite using `[← extensionEmbedding_completionConj hv, ← map_mul, hx, map_one]`.

Take `⟨u, hu0, hu⟩` from `exists_conj_eq_mul hz`. Take `⟨y, rfl⟩` from `surjective_extensionEmbedding_of_isComplex hw u`. Establish `hy0 : y ≠ 0` using `by rintro rfl; exact hu0 (map_zero _)`. Use `⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩` and prove the remaining obligations. Apply `Additive.toMul.injective` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[cycSub_unitsRep_toMul, toMul_ofMul, Units.val_mk0, div_eq_iff hy0]`. Apply `(extensionEmbedding w).injective` to reduce the goal to its premises. Rewrite using `[extensionEmbedding_completionConj, hu, map_mul]`.
-/
theorem natCard_kerModRange_normHom_cycSub (hv : v.IsReal) (hw : w.IsComplex) :
    Nat.card (KerModRange (normHom (unitsRep v w))
      (cycSub (unitsRep v w) (completionConj hv))) = 1 := by
  apply natCard_kerModRange_eq_one
  intro x hx
  rw [AddMonoidHom.mem_ker, ← toMul_eq_one, ← Units.val_eq_one, normHom_unitsRep_toMul hv hw] at hx
  have hz : extensionEmbedding w (x.toMul : w.Completion) *
      conj (extensionEmbedding w (x.toMul : w.Completion)) = 1 := by
    rw [← extensionEmbedding_completionConj hv, ← map_mul, hx, map_one]
  obtain ⟨u, hu0, hu⟩ := exists_conj_eq_mul hz
  obtain ⟨y, rfl⟩ := surjective_extensionEmbedding_of_isComplex hw u
  have hy0 : y ≠ 0 := by rintro rfl; exact hu0 (map_zero _)
  refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  rw [cycSub_unitsRep_toMul, toMul_ofMul, Units.val_mk0, div_eq_iff hy0]
  apply (extensionEmbedding w).injective
  rw [extensionEmbedding_completionConj, hu, map_mul]

/- English proof (translation)
Rewrite using `[cyclicHerbrand, herbrandQuotient, natCard_kerModRange_cycSub_normHom v w hv hw, natCard_kerModRange_normHom_cycSub v w hv hw]`. Evaluate the numerical expressions.
-/
theorem cyclicHerbrand_unitsRep_eq_two (hv : v.IsReal) (hw : w.IsComplex) :
    cyclicHerbrand (unitsRep v w) (completionConj hv) = 2 := by
  rw [cyclicHerbrand, herbrandQuotient, natCard_kerModRange_cycSub_normHom v w hv hw,
    natCard_kerModRange_normHom_cycSub v w hv hw]
  norm_num

/- English proof (translation)
Assemble the required witnesses or components as `⟨Nat.finite_of_card_ne_zero (by rw [natCard_kerModRange_cycSub_normHom v w hv hw]; norm_num), Nat.finite_of_card_ne_zero (by rw [natCard_kerModRange_normHom_cycSub v w hv hw]; norm_num)⟩`.
-/
theorem hasCyclicHerbrand_unitsRep (hv : v.IsReal) (hw : w.IsComplex) :
    HasCyclicHerbrand (unitsRep v w) (completionConj hv) :=
  ⟨Nat.finite_of_card_ne_zero (by rw [natCard_kerModRange_cycSub_normHom v w hv hw]; norm_num),
    Nat.finite_of_card_ne_zero (by rw [natCard_kerModRange_normHom_cycSub v w hv hw]; norm_num)⟩

/- English proof (translation)
Distinguish the cases in `h2 : v.IsReal ∧ w.IsComplex`. Take `⟨hv, hw⟩` from `h2`. Establish `hσc : σ = completionConj hv`. Break down `eq_one_or_eq_completionConj hv hw σ with h | h` into its components or cases. It suffices to derive a contradiction.

Use `hσ (completionConj hv)` as an intermediate fact. Rewrite `this` using `[h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot]`. Conclude with `completionConj_ne_one hv hw this`. Conclude with `h`. Rewrite using `[hσc, cyclicHerbrand_unitsRep_eq_two v w hv hw, (finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩]`.

Evaluate the numerical expressions. Rewrite using `[(finrank_completion_eq_one_iff w).2 h2]`. Use `subsingleton_gal w h2` as an intermediate fact. Establish `hsub : ∀ x, cycSub (unitsRep v w) σ x = 0` using `fun x => by`. Rewrite using `[Subsingleton.elim σ 1, cycSub_apply, map_one, Module.End.one_apply, sub_self]`.

Establish `hnorm : ∀ x, normHom (unitsRep v w) x = x` using `fun x => by`. Rewrite using `[normHom_apply, Fintype.sum_subsingleton _ 1, map_one, Module.End.one_apply]`. Rewrite using `[cyclicHerbrand, herbrandQuotient, natCard_kerModRange_eq_one (fun x _ => ⟨x, hnorm x⟩), natCard_kerModRange_eq_one (fun x hx => ⟨0, by`. Rewrite using `[map_zero]`. Rewrite `hx` using `[AddMonoidHom.mem_ker, hnorm]`.

Conclude with `hx.symm⟩)]`. Evaluate the numerical expressions.
-/
theorem cyclicHerbrand_unitsRep_eq_finrank (σ : Gal(w.Completion/v.Completion))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cyclicHerbrand (unitsRep v w) σ = Module.finrank v.Completion w.Completion := by
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · obtain ⟨hv, hw⟩ := h2
    have hσc : σ = completionConj hv := by
      rcases eq_one_or_eq_completionConj hv hw σ with h | h
      · exfalso
        have := hσ (completionConj hv)
        rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
        exact completionConj_ne_one hv hw this
      · exact h
    rw [hσc, cyclicHerbrand_unitsRep_eq_two v w hv hw, (finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩]
    norm_num
  · rw [(finrank_completion_eq_one_iff w).2 h2]
    have := subsingleton_gal w h2
    have hsub : ∀ x, cycSub (unitsRep v w) σ x = 0 := fun x => by
      rw [Subsingleton.elim σ 1, cycSub_apply, map_one, Module.End.one_apply, sub_self]
    have hnorm : ∀ x, normHom (unitsRep v w) x = x := fun x => by
      rw [normHom_apply, Fintype.sum_subsingleton _ 1, map_one, Module.End.one_apply]
    rw [cyclicHerbrand, herbrandQuotient, natCard_kerModRange_eq_one (fun x _ => ⟨x, hnorm x⟩),
      natCard_kerModRange_eq_one (fun x hx => ⟨0, by
        rw [map_zero]; rw [AddMonoidHom.mem_ker, hnorm] at hx; exact hx.symm⟩)]
    norm_num

end Herbrand

end InfinitePlace

end GroundTheory.Global
