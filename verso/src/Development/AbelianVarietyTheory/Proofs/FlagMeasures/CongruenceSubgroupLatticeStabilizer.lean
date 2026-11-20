import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPowSmulMem

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CongFin

section Abstract

variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {O : Subring E}

/- English proof (translation)
Rewrite using `[MulAction.mem_stabilizer_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Rewrite `hv` using `[← h, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨w, hw, hwv⟩` from `hv`. Establish `: w = v` using `g.injective hwv`. Conclude with `this ▸ hw`. Introduce `hv`.

Rewrite using `[← h, Submodule.mem_smul_pointwise_iff_exists]`. Conclude with `⟨v, hv, rfl⟩`. Introduce `h`. Use extensionality with `v`. Rewrite using `[Submodule.mem_smul_pointwise_iff_exists]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `(h w).2 hw`. Introduce `hv`. Use `⟨g.symm v, (h _).1 (by simpa using hv), ?_⟩` and prove the remaining obligations.

Conclude with `g.apply_symm_apply v`.
-/
theorem mem_stab_iff (Λ : Submodule O V) (g : V ≃ₗ[E] V) :
    g ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ ↔ ∀ v, g v ∈ Λ ↔ v ∈ Λ := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h v
    constructor
    · intro hv
      rw [← h, Submodule.mem_smul_pointwise_iff_exists] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have : w = v := g.injective hwv
      exact this ▸ hw
    · intro hv
      rw [← h, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext v
    rw [Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).2 hw
    · intro hv
      refine ⟨g.symm v, (h _).1 (by simpa using hv), ?_⟩
      exact g.apply_symm_apply v

/- English proof (translation)
The claim follows from `Λ.smul_mem ⟨c, hc⟩ hv`.
-/
theorem smul_mem_of (Λ : Submodule O V) {c : E} (hc : c ∈ O) {v : V} (hv : v ∈ Λ) : c • v ∈ Λ :=
  Λ.smul_mem ⟨c, hc⟩ hv

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PowSmulMem.main`. Consider the case `exact _root_.GlobalTheory.PowSmulMem.main`. Consider the case `(apply _root_.GlobalTheory.PowSmulMem.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PowSmulMem.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PowSmulMem.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PowSmulMem.main ..)`.
-/
theorem exists_pow_smul_mem {p : E} (hp : p ∈ O) (hdiv : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ Λ' : Submodule O V) (hΛ : Λ.FG) (hΛ' : Submodule.span E (Λ' : Set V) = ⊤) :
    ∃ a : ℕ, ∀ v ∈ Λ, p ^ a • v ∈ Λ' := by
  first
  | exact @_root_.GlobalTheory.PowSmulMem.main
  | exact _root_.GlobalTheory.PowSmulMem.main
  | (apply _root_.GlobalTheory.PowSmulMem.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowSmulMem.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowSmulMem.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowSmulMem.main ..)

def congSub (Λ : Submodule O V) (c : E) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | g ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ ∧ ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = c • w}
  one_mem' := ⟨one_mem _, fun v _ => ⟨0, Λ.zero_mem, by simp⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun v hv => ?_⟩
    obtain ⟨w, hw, h⟩ := hb' v hv
    obtain ⟨w', hw', h'⟩ := ha' (b v) (((mem_stab_iff Λ b).1 hb v).2 hv)
    refine ⟨w' + w, Λ.add_mem hw' hw, ?_⟩
    rw [smul_add, ← h, ← h']
    simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun v hv => ?_⟩
    obtain ⟨w, hw, h⟩ := ha' (a⁻¹ v) (((mem_stab_iff Λ _).1 (inv_mem ha) v).2 hv)
    refine ⟨-w, Λ.neg_mem hw, ?_⟩
    have : a (a⁻¹ v) = v := a.apply_symm_apply v
    rw [smul_neg, ← h, this, neg_sub]

/- English proof (translation)
Use `⟨mul_mem (mul_mem ha hg.1) (inv_mem ha), fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, h⟩` from `hg.2 (a⁻¹ v) (((mem_stab_iff Λ _).1 (inv_mem ha) v).2 hv)`. Use `⟨a w, ((mem_stab_iff Λ _).1 ha w).2 hw, ?_⟩` and prove the remaining obligations. Establish `h2 : a (a⁻¹ v) = v` using `a.apply_symm_apply v`. Rewrite using `[← map_smul, ← h, map_sub, h2]`.

Both sides reduce to the same expression.
-/
theorem conj_mem (Λ : Submodule O V) (c : E) {a g : V ≃ₗ[E] V}
    (ha : a ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ) (hg : g ∈ congSub Λ c) :
    a * g * a⁻¹ ∈ congSub Λ c := by
  refine ⟨mul_mem (mul_mem ha hg.1) (inv_mem ha), fun v hv => ?_⟩
  obtain ⟨w, hw, h⟩ := hg.2 (a⁻¹ v) (((mem_stab_iff Λ _).1 (inv_mem ha) v).2 hv)
  refine ⟨a w, ((mem_stab_iff Λ _).1 ha w).2 hw, ?_⟩
  have h2 : a (a⁻¹ v) = v := a.apply_symm_apply v
  rw [← map_smul, ← h, map_sub, h2]
  rfl

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[Subgroup.mem_pointwise_smul_iff_inv_smul_mem]`. Establish `e : (MulAut.conj a)⁻¹ • g = a⁻¹ * g * a⁻¹⁻¹` using `by simp`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `conj_mem Λ c ha h` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Conclude with `conj_mem Λ c (inv_mem ha)`.
-/
theorem conj_smul_eq (Λ : Submodule O V) (c : E) {a : V ≃ₗ[E] V}
    (ha : a ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ) :
    MulAut.conj a • congSub Λ c = congSub Λ c := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have e : (MulAut.conj a)⁻¹ • g = a⁻¹ * g * a⁻¹⁻¹ := by simp
  rw [e]
  constructor
  · intro h
    have := conj_mem Λ c ha h
    simpa [mul_assoc] using this
  · exact conj_mem Λ c (inv_mem ha)

/- English proof (translation)
Use `set I : Ideal O := Ideal.span {(⟨c, hc⟩ : O)} with hI`. Use `haveI : Module.Finite O Λ := Module.Finite.iff_fg.2 hΛ`. Use `haveI : Finite (Λ ⧸ (I • ⊤ : Submodule O Λ)) := Submodule.finite_quotient_smul I (Module.Finite.fg_top)`. Establish `hQ : ∀ x y : Λ, (Submodule.Quotient.mk x : Λ ⧸ (I • ⊤ : Submodule O Λ)) = Submodule.Quotient.mk y → ∃ w ∈ Λ, (x : V) - y = c • w`. Introduce `x y h`.

Rewrite `h` using `[Submodule.Quotient.eq, hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨w, -, hw⟩` from `h`. Conclude with `⟨w, w.2, (congrArg Subtype.val hw).symm⟩`. Use `set S := MulAction.stabilizer (V ≃ₗ[E] V) Λ`. Set `f : S → (Λ ⧸ (I • ⊤ : Submodule O Λ)) → (Λ ⧸ (I • ⊤ : Submodule O Λ))` to `fun g q => Submodule.Quotient.mk ⟨g.1 (q.out : Λ), ((mem_stab_iff Λ _).1 g.2 _).2 q.out.2⟩`.

Establish `hf : ∀ g h : S, f g = f h → g⁻¹ * h ∈ (congSub Λ c).subgroupOf S`. Introduce `g h hgh`. Rewrite using `[Subgroup.mem_subgroupOf]`. Use `⟨(g⁻¹ * h).2, fun v hv => ?_⟩` and prove the remaining obligations. Set `q : Λ ⧸ (I • ⊤ : Submodule O Λ)` to `Submodule.Quotient.mk ⟨v, hv⟩`.

Take `⟨w, hw, e1⟩` from `hQ ⟨v, hv⟩ q.out (Quotient.out_eq q).symm`. Take `⟨w', hw', e2⟩` from `hQ _ _ (congrFun hgh q).symm`. Establish `hi` using `(mem_stab_iff Λ _).1 (inv_mem g.2)`. Establish `hh` using `(mem_stab_iff Λ _).1 h.2`. Use `⟨g.1⁻¹ (h.1 w) + g.1⁻¹ w' - w, Λ.sub_mem (Λ.add_mem ((hi _).2 ((hh _).2 hw)) ((hi _).2 hw')) hw, ?_⟩` and prove the remaining obligations.

Establish `e3 : v = (q.out : Λ) + c • w` using `by rw [← e1]; simp`. Establish `e4 : h.1 (q.out : Λ) = g.1 (q.out : Λ) + c • w'` using `by rw [← e2]; simp`. Establish `e5 : ∀ x, g.1⁻¹ (g.1 x) = x` using `fun x => g.1.symm_apply_apply x`. Use `show g.1⁻¹ (h.1 v) - v = _`. Rewrite using `[e3, map_add, e4]`.

Simplify using `only [map_add, map_smul, e5, smul_add, smul_sub]`. Normalize the expressions using the abelian group laws. Establish `: Finite (S ⧸ (congSub Λ c).subgroupOf S)`. Use `Finite.of_injective (fun q => f q.out) fun q q' h => ?_` and prove the remaining obligations. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]`.

Conclude with `hf _ _ h`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero (Λ : Submodule O V) (hΛ : Λ.FG) {c : E} (hc : c ∈ O)
    (hfin : Finite (O ⧸ Ideal.span {(⟨c, hc⟩ : O)})) :
    (congSub Λ c).relIndex (MulAction.stabilizer (V ≃ₗ[E] V) Λ) ≠ 0 := by
  set I : Ideal O := Ideal.span {(⟨c, hc⟩ : O)} with hI
  haveI : Module.Finite O Λ := Module.Finite.iff_fg.2 hΛ
  haveI : Finite (Λ ⧸ (I • ⊤ : Submodule O Λ)) :=
    Submodule.finite_quotient_smul I (Module.Finite.fg_top)
  have hQ : ∀ x y : Λ, (Submodule.Quotient.mk x : Λ ⧸ (I • ⊤ : Submodule O Λ)) = Submodule.Quotient.mk y →
      ∃ w ∈ Λ, (x : V) - y = c • w := by
    intro x y h
    rw [Submodule.Quotient.eq, hI, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨w, -, hw⟩ := h
    exact ⟨w, w.2, (congrArg Subtype.val hw).symm⟩
  set S := MulAction.stabilizer (V ≃ₗ[E] V) Λ
  let f : S → (Λ ⧸ (I • ⊤ : Submodule O Λ)) → (Λ ⧸ (I • ⊤ : Submodule O Λ)) :=
    fun g q => Submodule.Quotient.mk ⟨g.1 (q.out : Λ), ((mem_stab_iff Λ _).1 g.2 _).2 q.out.2⟩
  have hf : ∀ g h : S, f g = f h → g⁻¹ * h ∈ (congSub Λ c).subgroupOf S := by
    intro g h hgh
    rw [Subgroup.mem_subgroupOf]
    refine ⟨(g⁻¹ * h).2, fun v hv => ?_⟩
    let q : Λ ⧸ (I • ⊤ : Submodule O Λ) := Submodule.Quotient.mk ⟨v, hv⟩
    obtain ⟨w, hw, e1⟩ := hQ ⟨v, hv⟩ q.out (Quotient.out_eq q).symm
    obtain ⟨w', hw', e2⟩ := hQ _ _ (congrFun hgh q).symm
    have hi := (mem_stab_iff Λ _).1 (inv_mem g.2)
    have hh := (mem_stab_iff Λ _).1 h.2
    refine ⟨g.1⁻¹ (h.1 w) + g.1⁻¹ w' - w,
      Λ.sub_mem (Λ.add_mem ((hi _).2 ((hh _).2 hw)) ((hi _).2 hw')) hw, ?_⟩
    have e3 : v = (q.out : Λ) + c • w := by rw [← e1]; simp
    have e4 : h.1 (q.out : Λ) = g.1 (q.out : Λ) + c • w' := by rw [← e2]; simp
    have e5 : ∀ x, g.1⁻¹ (g.1 x) = x := fun x => g.1.symm_apply_apply x
    show g.1⁻¹ (h.1 v) - v = _
    rw [e3, map_add, e4]
    simp only [map_add, map_smul, e5, smul_add, smul_sub]
    abel
  have : Finite (S ⧸ (congSub Λ c).subgroupOf S) := by
    refine Finite.of_injective (fun q => f q.out) fun q q' h => ?_
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
    exact hf _ _ h
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Establish `hg1 : ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = p • w`. Introduce `v hv`. Take `⟨w, hw, h⟩` from `hg v hv`. Take `⟨M, rfl⟩` from `Nat.exists_eq_add_of_le hN`. Conclude with `⟨p ^ M • w, smul_mem_of Λ (O.pow_mem hp M) hw, by rw [h, pow_add, pow_one, mul_smul]⟩`.

Establish `hle : ∀ v ∈ Λ, g v ∈ Λ`. Introduce `v hv`. Take `⟨w, hw, h⟩` from `hg1 v hv`. Rewrite using `[eq_add_of_sub_eq h]`. Conclude with `Λ.add_mem (smul_mem_of Λ hp hw) hv`.

Establish `hit : ∀ k : ℕ, ∀ v ∈ Λ, ∃ u ∈ Λ, ∃ w ∈ Λ, v = g u + p ^ k • w`. Introduce `k v hv`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, Λ.zero_mem, v, hv, by simp⟩`. Consider the case `succ k ih`.

Take `⟨u, hu, w, hw, e⟩` from `ih`. Take `⟨w', hw', e'⟩` from `hg1 w hw`. Use `⟨u + p ^ k • w, Λ.add_mem hu (smul_mem_of Λ (O.pow_mem hp k) hw), -w', Λ.neg_mem hw', ?_⟩` and prove the remaining obligations. Rewrite using `[e, map_add, map_smul, eq_add_of_sub_eq e', pow_succ, mul_smul]`. Simplify using `only [smul_add, smul_neg]`.

Normalize the expressions using the abelian group laws. Set `Λ1 : Submodule O V` to `Λ.map (g.symm.toLinearMap.restrictScalars O)`. Take `⟨a, ha⟩` from `exists_pow_smul_mem hp hdiv Λ1 Λ (hΛ.map _) hΛ'`. Rewrite using `[mem_stab_iff]`. Use `fun v => ⟨fun hv => ?_, hle v⟩` and prove the remaining obligations.

Take `⟨u, hu, w, hw, e⟩` from `hit a _ hv`. Establish `: v = u + p ^ a • g.symm w` using `g.injective (by rw [e]; simp)`. Rewrite using `[this]`. Conclude with `Λ.add_mem hu (ha _ ⟨w, hw, rfl⟩)`.
-/
theorem mem_stab_of_cong {p : E} (hp : p ∈ O) (hdiv : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ : Submodule O V) (hΛ : Λ.FG) (hΛ' : Submodule.span E (Λ : Set V) = ⊤) {N : ℕ} (hN : 1 ≤ N)
    (g : V ≃ₗ[E] V) (hg : ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = p ^ N • w) :
    g ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ := by
  have hg1 : ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = p • w := by
    intro v hv
    obtain ⟨w, hw, h⟩ := hg v hv
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
    exact ⟨p ^ M • w, smul_mem_of Λ (O.pow_mem hp M) hw, by rw [h, pow_add, pow_one, mul_smul]⟩
  have hle : ∀ v ∈ Λ, g v ∈ Λ := by
    intro v hv
    obtain ⟨w, hw, h⟩ := hg1 v hv
    rw [eq_add_of_sub_eq h]
    exact Λ.add_mem (smul_mem_of Λ hp hw) hv
  have hit : ∀ k : ℕ, ∀ v ∈ Λ, ∃ u ∈ Λ, ∃ w ∈ Λ, v = g u + p ^ k • w := by
    intro k v hv
    induction k with
    | zero => exact ⟨0, Λ.zero_mem, v, hv, by simp⟩
    | succ k ih =>
      obtain ⟨u, hu, w, hw, e⟩ := ih
      obtain ⟨w', hw', e'⟩ := hg1 w hw
      refine ⟨u + p ^ k • w, Λ.add_mem hu (smul_mem_of Λ (O.pow_mem hp k) hw), -w',
        Λ.neg_mem hw', ?_⟩
      rw [e, map_add, map_smul, eq_add_of_sub_eq e', pow_succ, mul_smul]
      simp only [smul_add, smul_neg]
      abel
  let Λ1 : Submodule O V := Λ.map (g.symm.toLinearMap.restrictScalars O)
  obtain ⟨a, ha⟩ := exists_pow_smul_mem hp hdiv Λ1 Λ (hΛ.map _) hΛ'
  rw [mem_stab_iff]
  refine fun v => ⟨fun hv => ?_, hle v⟩
  obtain ⟨u, hu, w, hw, e⟩ := hit a _ hv
  have : v = u + p ^ a • g.symm w := g.injective (by rw [e]; simp)
  rw [this]
  exact Λ.add_mem hu (ha _ ⟨w, hw, rfl⟩)

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_pow_smul_mem hp hdiv Λ Λ' hΛ hs'`. Take `⟨b, hb⟩` from `exists_pow_smul_mem hp hdiv Λ' Λ hΛ' hs`. Use `⟨b + (N + a), fun g hg v hv => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, e⟩` from `hg _ (hb v hv)`. Use `⟨p ^ a • w, ha w hw, ?_⟩` and prove the remaining obligations.

Rewrite `e` using `[map_smul, ← smul_sub, pow_add, mul_smul, pow_add, mul_smul]`. Conclude with `(hu.pow b).smul_left_cancel.1 e`.
-/
theorem exists_level {p : E} (hp : p ∈ O) (hu : IsUnit p) (hdiv : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ Λ' : Submodule O V) (hΛ : Λ.FG) (hs : Submodule.span E (Λ : Set V) = ⊤)
    (hΛ' : Λ'.FG) (hs' : Submodule.span E (Λ' : Set V) = ⊤) (N : ℕ) :
    ∃ N' : ℕ, ∀ g : V ≃ₗ[E] V, (∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = p ^ N' • w) →
      ∀ v ∈ Λ', ∃ w ∈ Λ', g v - v = p ^ N • w := by
  obtain ⟨a, ha⟩ := exists_pow_smul_mem hp hdiv Λ Λ' hΛ hs'
  obtain ⟨b, hb⟩ := exists_pow_smul_mem hp hdiv Λ' Λ hΛ' hs
  refine ⟨b + (N + a), fun g hg v hv => ?_⟩
  obtain ⟨w, hw, e⟩ := hg _ (hb v hv)
  refine ⟨p ^ a • w, ha w hw, ?_⟩
  rw [map_smul, ← smul_sub, pow_add, mul_smul, pow_add, mul_smul] at e
  exact (hu.pow b).smul_left_cancel.1 e

end Abstract

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Use `haveI := L.free`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)`. Take `⟨y, hy, hi⟩` from `((IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic e)).exists_integral_multiple`. Take `⟨a, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ`. Use `⟨a, (L.O_def _).2 ?_⟩` and prove the remaining obligations.

Establish `h` using `hi.smul (u⁻¹ : (𝒪[F])ˣ).1`. Rewrite `h` using `[smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow]`. Conclude with `h`.
-/
theorem exists_pow_mul_mem (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (e : E) :
    ∃ a : ℕ, algebraMap F E ϖ ^ a * e ∈ L.O := by
  haveI := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  obtain ⟨y, hy, hi⟩ := ((IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2
    (Algebra.IsAlgebraic.isAlgebraic e)).exists_integral_multiple
  obtain ⟨a, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  refine ⟨a, (L.O_def _).2 ?_⟩
  have h := hi.smul (u⁻¹ : (𝒪[F])ˣ).1
  rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow] at h
  exact h

end GlobalTheory.HL.CongFin

open GlobalTheory.HL.CongFin in

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L ϖ hϖ n Λ hΛ N`. Take `⟨-, -, -, -, hO, hcard, hq, -⟩` from `GlobalTheory.UnramOrder.order_facts L ϖ hϖ`. Establish `hp : algebraMap F E ϖ ∈ L.O` using `(hO _).2 ϖ.2`. Establish `hu : IsUnit (algebraMap F E ϖ)` using `(IsUnit.mk0 (ϖ : F) (fun h => hϖ.ne_zero (Subtype.ext h))).map _`. Establish `hdiv` using `exists_pow_mul_mem L ϖ hϖ`.

Simplify using `only [CongId, map_pow]`. Use `⟨⟨congSub Λ (algebraMap F E ϖ ^ N), fun g => Iff.rfl, ?_, fun a ha => conj_smul_eq Λ _ ha⟩, fun hN g hg => mem_stab_of_cong hp hdiv Λ hΛ.1 hΛ.2 hN g hg, fun Λ' hΛ' => exists_level hp hu hdiv Λ Λ' hΛ.1 hΛ.2 hΛ'.1 hΛ'.2 N⟩` and prove the remaining obligations. Use `relIndex_ne_zero Λ hΛ.1 (L.O.pow_mem hp N) ?_` and prove the remaining obligations. Establish `hs : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ N)} = {(⟨algebraMap F E ϖ ^ N, L.O.pow_mem hp N⟩ : L.O)}`. Use extensionality with `y`.

Simplify using `[Subtype.ext_iff]`. Establish `h` using `hcard N`. Rewrite `h` using `[hs]`. Use `Nat.finite_of_card_ne_zero ?_` and prove the remaining obligations. Rewrite using `[h]`.

Conclude with `pow_ne_zero _ (by omega)`.
-/
theorem GlobalTheory.HL.congruence_subgroup_facts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Λ : Submodule L.O (Fin n → E)), IsLat L Λ → ∀ N : ℕ, (∃ K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (∀ g, g ∈ K ↔ g ∈ stabL L Λ ∧ CongId L ϖ Λ N g) ∧ K.relIndex (stabL L Λ) ≠ 0 ∧ ∀ a ∈ stabL L Λ, MulAut.conj a • K = K) ∧ (1 ≤ N → ∀ g, CongId L ϖ Λ N g → g ∈ stabL L Λ) ∧ ∀ Λ', IsLat L Λ' → ∃ N' : ℕ, ∀ g, CongId L ϖ Λ N' g → CongId L ϖ Λ' N g := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Λ hΛ N
  obtain ⟨-, -, -, -, hO, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hp : algebraMap F E ϖ ∈ L.O := (hO _).2 ϖ.2
  have hu : IsUnit (algebraMap F E ϖ) :=
    (IsUnit.mk0 (ϖ : F) (fun h => hϖ.ne_zero (Subtype.ext h))).map _
  have hdiv := exists_pow_mul_mem L ϖ hϖ
  simp only [CongId, map_pow]
  refine ⟨⟨congSub Λ (algebraMap F E ϖ ^ N), fun g => Iff.rfl, ?_, fun a ha => conj_smul_eq Λ _ ha⟩,
    fun hN g hg => mem_stab_of_cong hp hdiv Λ hΛ.1 hΛ.2 hN g hg,
    fun Λ' hΛ' => exists_level hp hu hdiv Λ Λ' hΛ.1 hΛ.2 hΛ'.1 hΛ'.2 N⟩
  refine relIndex_ne_zero Λ hΛ.1 (L.O.pow_mem hp N) ?_
  have hs : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ N)}
      = {(⟨algebraMap F E ϖ ^ N, L.O.pow_mem hp N⟩ : L.O)} := by
    ext y; simp [Subtype.ext_iff]
  have h := hcard N
  rw [hs] at h
  refine Nat.finite_of_card_ne_zero ?_
  rw [h]
  exact pow_ne_zero _ (by omega)
