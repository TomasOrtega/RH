import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqNormSumRepsMulIndexLe

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate

namespace GlobalTheory.HL.DivisibleGauss

/- English proof (translation)
Establish `hb : Function.Bijective fun w : R => (QuotientAddGroup.mk (⟨w, hRM w w.2⟩ : M) : M ⧸ P.addSubgroupOf M)`. Prove the components needed by the constructor for the conclusion. Introduce `w w' h`. Establish `h'` using `QuotientAddGroup.eq_iff_sub_mem.1 h`. Conclude with `Subtype.ext ((hR w (hRM w w.2)).unique ⟨w.2, by simp⟩ ⟨w'.2, h'⟩)`.

Introduce `x`. Take `⟨u, rfl⟩` from `QuotientAddGroup.mk_surjective x`. Take `⟨w, ⟨hw, hw'⟩, -⟩` from `hR u u.2`. Conclude with `⟨⟨w, hw⟩, (QuotientAddGroup.eq_iff_sub_mem.2 (show u - ⟨w, hRM w hw⟩ ∈ P.addSubgroupOf M from hw')).symm⟩`. Rewrite using `[← Fintype.card_coe, ← Nat.card_eq_fintype_card]`.

Conclude with `Nat.card_eq_of_bijective _ hb`.
-/
theorem card_reps_eq_relIndex {V : Type*} [AddCommGroup V] (M P : AddSubgroup V) (R : Finset V)
    (hRM : ∀ u ∈ R, u ∈ M) (hR : ∀ u ∈ M, ∃! w, w ∈ R ∧ u - w ∈ P) :
    R.card = P.relIndex M := by
  have hb : Function.Bijective fun w : R =>
      (QuotientAddGroup.mk (⟨w, hRM w w.2⟩ : M) : M ⧸ P.addSubgroupOf M) := by
    constructor
    · intro w w' h
      have h' := QuotientAddGroup.eq_iff_sub_mem.1 h
      exact Subtype.ext ((hR w (hRM w w.2)).unique ⟨w.2, by simp⟩ ⟨w'.2, h'⟩)
    · intro x
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨w, ⟨hw, hw'⟩, -⟩ := hR u u.2
      exact ⟨⟨w, hw⟩, (QuotientAddGroup.eq_iff_sub_mem.2
        (show u - ⟨w, hRM w hw⟩ ∈ P.addSubgroupOf M from hw')).symm⟩
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_eq_of_bijective _ hb

/- English proof (translation)
Establish `hinj : Function.Injective (Subtype.val : M → V)` using `Subtype.val_injective`. Establish `hrange : ∀ u ∈ R, u ∈ Set.range (Subtype.val : M → V)` using `fun u hu => ⟨⟨u, hRM u hu⟩, rfl⟩`. Establish `key` using `GaussSum.sq_norm_sum_reps_mul_index_le (P.addSubgroupOf M) (Q.addSubgroupOf M) (AddSubgroup.comap_mono hPQ) (R.preimage Subtype.val hinj.injOn) ?_ (fun m => f m) (fun m => hf m) (fun u p hp => hP u u.2 p hp) ?_`. Rewrite `key` using `[Finset.sum_preimage Subtype.val R hinj.injOn f (fun u hu h => (h (hrange u hu)).elim), Finset.card_preimage, Finset.filter_true_of_mem hrange]`. Then use the resulting hypothesis. Introduce `u`.

Take `⟨w, ⟨hw, hw'⟩, huniq⟩` from `hR u u.2`. Use `⟨⟨w, hRM w hw⟩, ⟨Finset.mem_preimage.2 hw, hw'⟩, fun y hy => hinj ?_⟩` and prove the remaining obligations. Conclude with `huniq _ ⟨Finset.mem_preimage.1 hy.1, hy.2⟩`. Introduce `h hh`. Take `⟨v, hv, c, hc, H⟩` from `hQ h h.2 hh`.

Conclude with `⟨⟨v, hv⟩, c, hc, fun u => H u u.2⟩`.
-/
theorem sq_norm_sum_mul_relIndex_le {V : Type*} [AddCommGroup V] (M P Q : AddSubgroup V)
    (hPQ : P ≤ Q) (R : Finset V) (hRM : ∀ u ∈ R, u ∈ M)
    (hR : ∀ u ∈ M, ∃! w, w ∈ R ∧ u - w ∈ P)
    (f : V → ℂ) (hf : ∀ u, ‖f u‖ = 1) (hP : ∀ u ∈ M, ∀ p ∈ P, f (u + p) = f u)
    (hQ : ∀ h ∈ M, h ∉ Q → ∃ v ∈ M, ∃ c : ℂ, c ≠ 1 ∧
      ∀ u ∈ M, f (u + v + h) * conj (f (u + v)) = c * (f (u + h) * conj (f u))) :
    ‖∑ u ∈ R, f u‖ ^ 2 * (Q.relIndex M : ℝ) ≤ (R.card : ℝ) ^ 2 := by
  have hinj : Function.Injective (Subtype.val : M → V) := Subtype.val_injective
  have hrange : ∀ u ∈ R, u ∈ Set.range (Subtype.val : M → V) := fun u hu => ⟨⟨u, hRM u hu⟩, rfl⟩
  have key := GaussSum.sq_norm_sum_reps_mul_index_le (P.addSubgroupOf M) (Q.addSubgroupOf M)
    (AddSubgroup.comap_mono hPQ) (R.preimage Subtype.val hinj.injOn) ?_ (fun m => f m)
    (fun m => hf m) (fun u p hp => hP u u.2 p hp) ?_
  · rwa [Finset.sum_preimage Subtype.val R hinj.injOn f
      (fun u hu h => (h (hrange u hu)).elim), Finset.card_preimage,
      Finset.filter_true_of_mem hrange] at key
  · intro u
    obtain ⟨w, ⟨hw, hw'⟩, huniq⟩ := hR u u.2
    refine ⟨⟨w, hRM w hw⟩, ⟨Finset.mem_preimage.2 hw, hw'⟩, fun y hy => hinj ?_⟩
    exact huniq _ ⟨Finset.mem_preimage.1 hy.1, hy.2⟩
  · intro h hh
    obtain ⟨v, hv, c, hc, H⟩ := hQ h h.2 hh
    exact ⟨⟨v, hv⟩, c, hc, fun u => H u u.2⟩

/- English proof (translation)
Establish `hinj : Function.Injective (AddMonoidHom.mulLeft x)` using `(injective_iff_map_eq_zero _).2 hx`. Establish `h1 : (Ideal.span {x * y}).toAddSubgroup = (Ideal.span {y}).toAddSubgroup.map (AddMonoidHom.mulLeft x)`. Use extensionality with `z`. Simplify using `only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨y * c, dvd_mul_right _ _, (mul_assoc _ _ _).symm⟩`. Introduce and unpack `⟨_, ⟨c, rfl⟩, rfl⟩`. Conclude with `⟨c, (mul_assoc _ _ _).symm⟩`. Establish `h2 : (Ideal.span {x}).toAddSubgroup = (⊤ : AddSubgroup A).map (AddMonoidHom.mulLeft x)`.

Use extensionality with `z`. Simplify using `only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨c, trivial, rfl⟩`.

Introduce and unpack `⟨c, -, rfl⟩`. Conclude with `⟨c, rfl⟩`. Establish `h3 : (Ideal.span {x * y}).toAddSubgroup ≤ (Ideal.span {x}).toAddSubgroup` using `fun z hz => Ideal.mem_span_singleton.2 ((dvd_mul_right x y).trans (Ideal.mem_span_singleton.1 hz))`. Rewrite using `[← AddSubgroup.relIndex_mul_index h3]`. Use `congr 1`.

Rewrite using `[h1, h2, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_top_right]`.
-/
theorem index_span_mul {A : Type*} [CommRing A] (x y : A) (hx : ∀ z, x * z = 0 → z = 0) :
    (Ideal.span {x * y}).toAddSubgroup.index
      = (Ideal.span {y}).toAddSubgroup.index * (Ideal.span {x}).toAddSubgroup.index := by
  have hinj : Function.Injective (AddMonoidHom.mulLeft x) :=
    (injective_iff_map_eq_zero _).2 hx
  have h1 : (Ideal.span {x * y}).toAddSubgroup
      = (Ideal.span {y}).toAddSubgroup.map (AddMonoidHom.mulLeft x) := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨y * c, dvd_mul_right _ _, (mul_assoc _ _ _).symm⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, (mul_assoc _ _ _).symm⟩
  have h2 : (Ideal.span {x}).toAddSubgroup
      = (⊤ : AddSubgroup A).map (AddMonoidHom.mulLeft x) := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, trivial, rfl⟩
    · rintro ⟨c, -, rfl⟩
      exact ⟨c, rfl⟩
  have h3 : (Ideal.span {x * y}).toAddSubgroup ≤ (Ideal.span {x}).toAddSubgroup := fun z hz =>
    Ideal.mem_span_singleton.2 ((dvd_mul_right x y).trans (Ideal.mem_span_singleton.1 hz))
  rw [← AddSubgroup.relIndex_mul_index h3]
  congr 1
  rw [h1, h2, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_top_right]

/- English proof (translation)
Establish `hs : Function.Surjective c.toAddMonoidHom` using `fun z => ⟨c z, hc z⟩`. Rewrite using `[← AddSubgroup.index_comap_of_surjective _ hs]`. Use `congr 1`. Use extensionality with `z`. Simplify using `only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : c x ∣ c z` using `h`. Simplify `map_dvd c h'` using `only [hc]`. Conclude with `fun h => map_dvd c h`.
-/
theorem index_span_involution {A : Type*} [CommRing A] (c : A →+* A) (hc : ∀ x, c (c x) = x)
    (x : A) :
    (Ideal.span {c x}).toAddSubgroup.index = (Ideal.span {x}).toAddSubgroup.index := by
  have hs : Function.Surjective c.toAddMonoidHom := fun z => ⟨c z, hc z⟩
  rw [← AddSubgroup.index_comap_of_surjective _ hs]
  congr 1
  ext z
  simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
  constructor
  · intro h
    have h' : c x ∣ c z := h
    simpa only [hc] using map_dvd c h'
  · exact fun h => map_dvd c h

section Form

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Simplify using `[hf, add_mul, Finset.sum_add_distrib]`.
-/
theorem form_add_left (a b y : Fin n → E) : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hf, mul_add, Finset.sum_add_distrib]`.
-/
theorem form_add_right (a b y : Fin n → E) : hf L Hm y (a + b) = hf L Hm y a + hf L Hm y b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hf, Finset.mul_sum, mul_assoc]`.
-/
theorem form_smul_left (c : E) (a y : Fin n → E) : hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem form_smul_right (c : E) (a y : Fin n → E) :
    hf L Hm y (c • a) = L.cj c * hf L Hm y a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `h' : ∀ i j, L.cj (Hm i j) = Hm j i` using `fun i j => congrFun (congrFun h j) i`. Simplify using `only [hf, map_sum, map_mul, L.cj_cj, h']`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem form_cj (h : IsHerm L Hm) (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by
  have h' : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h j) i
  simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def formLeft (y : Fin n → E) : (Fin n → E) →+ E :=
  AddMonoidHom.mk' (fun x => hf L Hm x y) fun a b => form_add_left L Hm a b y

def divBy (U : Submodule L.O (Fin n → E)) {ρ : ℕ} (e : Fin ρ → Fin n → E) (x : E) :
    AddSubgroup (Fin n → E) where
  carrier := {u | u ∈ U ∧ ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = x * c}
  zero_mem' := ⟨U.zero_mem, fun a => ⟨0, L.O.zero_mem, by simp [hf]⟩⟩
  add_mem' := by
    rintro u w ⟨hu, hu'⟩ ⟨hw, hw'⟩
    refine ⟨U.add_mem hu hw, fun a => ?_⟩
    obtain ⟨c, hc, h⟩ := hu' a
    obtain ⟨d, hd, h'⟩ := hw' a
    exact ⟨c + d, L.O.add_mem hc hd, by rw [form_add_left, h, h', mul_add]⟩
  neg_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨U.neg_mem hu, fun a => ?_⟩
    obtain ⟨c, hc, h⟩ := hu' a
    refine ⟨-c, L.O.neg_mem hc, ?_⟩
    rw [mul_neg, ← h]
    exact map_neg (formLeft L Hm (e a)) u

/- English proof (translation)
Set `φ : U.toAddSubgroup →+ (Fin ρ → L.O)` to `AddMonoidHom.mk' (fun u a => ⟨hf L Hm u (e a), hU u u.2 _ (he a)⟩) fun u w =>`. Use function extensionality and compare the values at `fun a => Subtype.ext (form_add_left L Hm _ _ _)`. Establish `hφ : Function.Surjective φ` using `fun c => by`. Use `⟨⟨∑ b, (c b : E) • e b, U.sum_mem fun b _ => U.smul_mem (c b) (he b)⟩,` and prove the remaining obligations. Use function extensionality and compare the values at `fun a => Subtype.ext ?_⟩`.

Use `show formLeft L Hm (e a) (∑ b, (c b : E) • e b) = c a`. Rewrite using `[map_sum]`. Use `show ∑ b, hf L Hm ((c b : E) • e b) (e a) = c a`. Simplify using `[form_smul_left, hee]`. Establish `h1 : (divBy L Hm U e x).addSubgroupOf U.toAddSubgroup = (AddSubgroup.pi Set.univ fun _ => (Ideal.span {x}).toAddSubgroup).comap φ`.

Use extensionality with `u`. Simplify using `only [AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, AddSubgroup.mem_addSubgroupOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩ a`. Take `⟨c, hc, h⟩` from `h a`.

Conclude with `⟨⟨c, hc⟩, Subtype.ext h⟩`. Use `fun h => ⟨u.2, fun a => ?_⟩` and prove the remaining obligations. Take `⟨c, h⟩` from `h a`. Conclude with `⟨c, c.2, congrArg Subtype.val h⟩`. Rewrite using `[AddSubgroup.relIndex, h1, AddSubgroup.index_comap_of_surjective _ hφ, AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem relIndex_divBy (U : Submodule L.O (Fin n → E))
    (hU : ∀ x ∈ U, ∀ y ∈ U, hf L Hm x y ∈ L.O) {ρ : ℕ} (e : Fin ρ → Fin n → E)
    (he : ∀ a, e a ∈ U) (hee : ∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) (x : L.O) :
    (divBy L Hm U e x).relIndex U.toAddSubgroup
      = (Ideal.span {x}).toAddSubgroup.index ^ ρ := by
  let φ : U.toAddSubgroup →+ (Fin ρ → L.O) :=
    AddMonoidHom.mk' (fun u a => ⟨hf L Hm u (e a), hU u u.2 _ (he a)⟩) fun u w =>
      funext fun a => Subtype.ext (form_add_left L Hm _ _ _)
  have hφ : Function.Surjective φ := fun c => by
    refine ⟨⟨∑ b, (c b : E) • e b, U.sum_mem fun b _ => U.smul_mem (c b) (he b)⟩,
      funext fun a => Subtype.ext ?_⟩
    show formLeft L Hm (e a) (∑ b, (c b : E) • e b) = c a
    rw [map_sum]
    show ∑ b, hf L Hm ((c b : E) • e b) (e a) = c a
    simp [form_smul_left, hee]
  have h1 : (divBy L Hm U e x).addSubgroupOf U.toAddSubgroup
      = (AddSubgroup.pi Set.univ fun _ => (Ideal.span {x}).toAddSubgroup).comap φ := by
    ext u
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ, true_implies,
      Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨-, h⟩ a
      obtain ⟨c, hc, h⟩ := h a
      exact ⟨⟨c, hc⟩, Subtype.ext h⟩
    · refine fun h => ⟨u.2, fun a => ?_⟩
      obtain ⟨c, h⟩ := h a
      exact ⟨c, c.2, congrArg Subtype.val h⟩
  rw [AddSubgroup.relIndex, h1, AddSubgroup.index_comap_of_surjective _ hφ,
    AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Form

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L n Hm hH ϖ hϖ ψ hψ1 hψ U hU ρ e he hee π j N hπ hππ hN R nrm hnrm hRU hR`. Take `⟨-, -, hdual, -, hint, hcard, hq, -⟩` from `GlobalTheory.UnramOrder.order_facts L ϖ hϖ`. Establish `hinj` using `GlobalTheory.UnramOrder.algebraMap_inj L`. Establish `hcj : ∀ {x}, x ∈ L.O → L.cj x ∈ L.O` using `fun hx => GlobalTheory.UnramOrder.cj_mem L hx`. Establish `hO : ∀ c : 𝒪[F], algebraMap F E c ∈ L.O` using `fun c => (hint c).2 c.2`.

Establish `hq0 : 0 < resQ ϖ` using `by omega`. Establish `hq0' : (0 : ℝ) < resQ ϖ` using `by exact_mod_cast hq0`. Set `p : ℕ → L.O` to `fun k => ⟨algebraMap F E ((ϖ : F) ^ k), hO (ϖ ^ k)⟩`. Establish `hp : ∀ k, (Ideal.span {p k}).toAddSubgroup.index = resQ ϖ ^ (2 * k)` using `fun k => by`. Establish `hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ k)} = {p k}`.

Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff, p]`. Rewrite using `[← hcard k, hset]`. Both sides reduce to the same expression. Set `π' : L.O` to `⟨π, hπ⟩`.

Establish `hϖ0 : (ϖ : F) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Establish `hπu : IsUnit π`. Use `(IsUnit.mk0 _ (pow_ne_zero j hϖ0)).map (algebraMap F E)` as an intermediate fact. Rewrite `this` using `[← hππ]`. Conclude with `isUnit_of_mul_isUnit_left this`.

Establish `hreg : ∀ z, π' * z = 0 → z = 0` using `fun z hz => Subtype.ext (hπu.mul_right_eq_zero.1 (congrArg Subtype.val hz))`. Establish `hπi : (Ideal.span {π'}).toAddSubgroup.index = resQ ϖ ^ j`. Set `c : L.O →+* L.O` to `(L.cj : E →+* E).restrict L.O L.O fun x hx => hcj hx`. Establish `h1` using `index_span_mul π' (c π') hreg`. Establish `h2 : π' * c π' = p j` using `Subtype.ext hππ`.

Rewrite `h1` using `[index_span_involution c (fun x => Subtype.ext (L.cj_cj x)), h2, hp, ← sq, mul_comm 2 j, pow_mul]`. Conclude with `(Nat.pow_left_injective two_ne_zero h1).symm`. Set `P : AddSubgroup (Fin n → E)` to `U.toAddSubgroup.map (DistribSMul.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ N)))`. Establish `hP : ∀ u, u ∈ P ↔ ∃ y ∈ U, u = algebraMap F E ((ϖ : F) ^ N) • y` using `fun u => ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩`. Establish `hPA : ∀ x : E, (∃ c ∈ L.O, algebraMap F E ((ϖ : F) ^ N) = x * c) → P ≤ divBy L Hm U e x`.

Introduce and unpack `x ⟨c, hc, hx⟩ u hu`. Take `⟨y, hy, rfl⟩` from `(hP u).1 hu`. Use `⟨U.smul_mem (p N) hy, fun a => ⟨c * hf L Hm y (e a), L.O.mul_mem hc (hU y hy _ (he a)), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[form_smul_left, hx, mul_assoc]`. Set `M` to `divBy L Hm U e π`.

Establish `hPM : P ≤ M` using `hPA π hN`. Establish `hMU : M ≤ U.toAddSubgroup` using `fun u hu => hu.1`. Establish `hMi : M.relIndex U.toAddSubgroup = (resQ ϖ ^ j) ^ ρ`. Rewrite using `[← hπi]`. Conclude with `relIndex_divBy L Hm U hU e he hee π'`.

Use `set R₀ := R.filter fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c with hR₀`. Establish `hR₀M : ∀ u ∈ R₀, u ∈ M` using `fun u hu => ⟨hRU u (Finset.mem_filter.1 hu).1, (Finset.mem_filter.1 hu).2⟩`. Establish `hR' : ∀ u ∈ U.toAddSubgroup, ∃! w, w ∈ R ∧ u - w ∈ P` using `fun u hu => by`. Simplify `hR u hu` using `only [hP]`. Establish `hR₀' : ∀ u ∈ M, ∃! w, w ∈ R₀ ∧ u - w ∈ P` using `fun u hu => by`.

Take `⟨w, ⟨hw, hw'⟩, huniq⟩` from `hR' u hu.1`. Establish `hwM : w ∈ M` using `by simpa using M.sub_mem hu (hPM hw')`. Conclude with `⟨w, ⟨Finset.mem_filter.2 ⟨hw, hwM.2⟩, hw'⟩, fun y hy => huniq y ⟨(Finset.mem_filter.1 hy.1).1, hy.2⟩⟩`. Establish `hshare : (R₀.card : ℝ) = (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ))`. Establish `h1` using `AddSubgroup.relIndex_mul_relIndex P M U.toAddSubgroup hPM hMU`.

Rewrite `h1` using `[hMi, ← card_reps_eq_relIndex M P R₀ hR₀M hR₀', ← card_reps_eq_relIndex U.toAddSubgroup P R hRU hR', ← pow_mul]`. Rewrite using `[zpow_neg, ← div_eq_mul_inv, eq_div_iff (by positivity)]`. Conclude with `h1` after adjusting the coercions. Use `⟨hshare, fun i hiN t u₀ ht => ?_⟩` and prove the remaining obligations. Rewrite using `[← hshare]`.

Use `set k := i - j with hk`. Set `Q` to `divBy L Hm U e (π * algebraMap F E ((ϖ : F) ^ k))`. Establish `hQM : Q ≤ M` using `fun u hu => ⟨hu.1, fun a => by`. Take `⟨c, hc, h⟩` from `hu.2 a`. Conclude with `⟨_, L.O.mul_mem (p k).2 hc, by rw [h, mul_assoc]⟩⟩`.

Establish `hQi : Q.relIndex M = (resQ ϖ ^ (k * ρ)) ^ 2`. Establish `h1` using `AddSubgroup.relIndex_mul_relIndex Q M U.toAddSubgroup hQM hMU`. Establish `h2 : Q.relIndex U.toAddSubgroup = _` using `relIndex_divBy L Hm U hU e he hee (π' * p k)`. Rewrite `h1` using `[hMi, h2, index_span_mul π' _ hreg, hp, hπi, mul_pow]`. Rewrite using `[Nat.eq_of_mul_eq_mul_right (by positivity) h1]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨m, hm⟩` from `Nat.exists_eq_add_of_le hiN`. Establish `hPQ : P ≤ Q`. Use `hPA _ ?_` and prove the remaining obligations. Break down `le_total i j with hij | hij` into its components or cases.

Establish `: k = 0` using `by omega`. Simplify `hN` using `only [this, pow_zero, map_one, mul_one]`. Use `⟨L.cj π * algebraMap F E ((ϖ : F) ^ m), L.O.mul_mem (hcj hπ) (p m).2, ?_⟩` and prove the remaining obligations. Establish `: N = j + k + m` using `by omega`. Rewrite using `[this, pow_add, pow_add, map_mul, map_mul, ← hππ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hτ : algebraMap F E t * algebraMap F E ((ϖ : F) ^ i) = algebraMap F E ((u₀ : 𝒪[F]) : F)` using `by rw [← map_mul, ht]`. Establish `key` using `sq_norm_sum_mul_relIndex_le M P Q hPQ R₀ hR₀M hR₀' (fun u => ψ (t * nrm u)) (fun u => hψ1 _) ?_ ?_`. Rewrite `key` using `[hQi, Nat.cast_pow, ← mul_pow]`. Establish `h` using `(sq_le_sq₀ (by positivity) (by positivity)).1 key`.

Rewrite using `[zpow_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]`. Conclude with `h` after adjusting the coercions. Introduce `u hu y' hy'`. Take `⟨y, hy, rfl⟩` from `(hP y').1 hy'`. Establish `h2 : algebraMap F E t * algebraMap F E ((ϖ : F) ^ N) ∈ L.O`.

Rewrite using `[hm, pow_add, map_mul, ← mul_assoc, hτ]`. Conclude with `L.O.mul_mem (hO _) (p m).2`. Establish `h3 : t * (nrm (u + algebraMap F E ((ϖ : F) ^ N) • y) - nrm u) ∈ 𝒪[F]`. Rewrite using `[← hint, map_mul, map_sub, hnrm, hnrm]`. Establish `: algebraMap F E t * (hf L Hm (u + algebraMap F E ((ϖ : F) ^ N) • y) (u + algebraMap F E ((ϖ : F) ^ N) • y) - hf L Hm u u) = algebraMap F E t * algebraMap F E ((ϖ : F) ^ N) * (hf L Hm u y + hf L Hm y u + algebraMap F E ((ϖ : F) ^ N) * hf L Hm y y)`.

Simplify using `only [form_add_left, form_add_right, form_smul_left, form_smul_right, AlgEquiv.commutes]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `L.O.mul_mem h2 (L.O.add_mem (L.O.add_mem (hU _ hu.1 _ hy) (hU _ hy _ hu.1)) (L.O.mul_mem (p N).2 (hU _ hy _ hy)))`. Establish `h4` using `(hψ _).2 h3 1`.

Establish `h5 : t * nrm (u + algebraMap F E ((ϖ : F) ^ N) • y) = t * nrm u + t * (nrm (u + algebraMap F E ((ϖ : F) ^ N) • y) - nrm u) * ((1 : 𝒪[F]) : F)` using `by push_cast; ring`. Use `show ψ _ = ψ _`. Rewrite using `[h5, AddChar.map_add_eq_mul, h4, mul_one]`. Introduce `h hM hh`. Take `⟨a, ha⟩` from `not_forall.1 fun h' => hh ⟨hM.1, h'⟩`.

Take `⟨c, hc, hca⟩` from `hM.2 a`. Establish `hij : i = j + k`. Assume the negation of the conclusion as `hne`. Establish `: k = 0` using `by omega`. Conclude with `ha ⟨c, hc, by rw [this, pow_zero, map_one, mul_one, hca]⟩`.

Use `set z := algebraMap F E (t * (ϖ : F) ^ j) * c with hz`. Establish `h1 : z ∉ L.O` using `fun h' => ha ⟨algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * z, L.O.mul_mem (hO _) h', by`. Establish `h2 : algebraMap F E ((u₀ : 𝒪[F]) : F) * algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) = 1`. Rewrite using `[← map_mul, ← Subring.coe_mul, Units.mul_inv]`. Simplify using the standard rewrite rules.

Rewrite `hτ` using `[hij, pow_add, map_mul]`. Rewrite using `[hca, hz, map_mul]`. Take the linear combination `(-(π * c)) * h2 - algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (π * c) * hτ⟩`. Take `⟨b, hb⟩` from `not_forall.1 fun h' => h1 (hdual _ h')`. Take `⟨hb, hb'⟩` from `Classical.not_imp.1 hb`.

Take `⟨s, hs⟩` from `(L.cj_fix (z * L.cj b + L.cj (z * L.cj b))).1 (by rw [map_add, L.cj_cj, add_comm])`. Establish `hs' : s ∉ 𝒪[F]` using `fun h' => hb' ⟨⟨s, h'⟩, hs.symm⟩`. Take `⟨y, hy⟩` from `not_forall.1 fun h' => hs' ((hψ s).1 h')`. Establish `hyb : algebraMap F E y * b ∈ L.O` using `L.O.mul_mem (hO y) hb`. Set `v : Fin n → E` to `(π * (algebraMap F E y * b)) • e a`.

Establish `hv : v ∈ M`. Use `⟨U.smul_mem (⟨_, L.O.mul_mem hπ hyb⟩ : L.O) (he a), fun a' => ⟨algebraMap F E y * b * hf L Hm (e a) (e a'), L.O.mul_mem hyb (hU _ (he a) _ (he a')), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[form_smul_left, mul_assoc]`. Use `⟨v, hv, ψ (s * y), hy, fun u _ => ?_⟩` and prove the remaining obligations. Establish `h2 : t * nrm (u + v + h) - t * nrm (u + v) = s * y + (t * nrm (u + h) - t * nrm u)`.

Apply `hinj` to reduce the goal to its premises. Establish `hca' : hf L Hm (e a) h = L.cj π * L.cj c`. Rewrite using `[← form_cj L Hm hH.1, hca, map_mul]`. Establish `h3 : hf L Hm v h + hf L Hm h v = algebraMap F E ((ϖ : F) ^ j) * (algebraMap F E y * (b * L.cj c + c * L.cj b))`. Simplify using `only [v, form_smul_left, form_smul_right, hca, hca', map_mul, AlgEquiv.commutes, ← hππ]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hz, map_mul, AlgEquiv.commutes, L.cj_cj] at hs`. Simplify using `only [map_sub, map_add (algebraMap F E), map_mul, hnrm, hs, form_add_left, form_add_right]`. Take the linear combination `algebraMap F E t * h3`. Use `show ψ _ * conj (ψ _) = _ * (ψ _ * conj (ψ _))`.

Rewrite using `[GaussSum.mul_conj_eq ψ hψ1, GaussSum.mul_conj_eq ψ hψ1, h2, AddChar.map_add_eq_mul]`.
-/
theorem share_and_gauss_sum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ψ : AddChar F ℂ), (∀ x : F, ‖ψ x‖ = 1) → (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ (UU : Submodule L.O (Fin n → E)), (∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O) → ∀ (ρ : ℕ) (e : Fin ρ → Fin n → E), (∀ a, e a ∈ UU) → (∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) → ∀ (π : E) (j N : ℕ), π ∈ L.O → π * L.cj π = algebraMap F E ((ϖ : F) ^ j) → (∃ c ∈ L.O, algebraMap F E ((ϖ : F) ^ N) = π * c) → ∀ (R : Finset (Fin n → E)) (nrm : (Fin n → E) → F), (∀ u, algebraMap F E (nrm u) = hf L Hm u u) → (∀ u ∈ R, u ∈ UU) → (∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y) → ((R.filter fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c).card : ℝ) = (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) ∧ ∀ (i : ℕ), i ≤ N → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ‖∑ u ∈ R.filter (fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c), ψ (t * nrm u)‖ ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ)) := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH ϖ hϖ ψ hψ1 hψ U hU ρ e he hee π j N hπ hππ hN R nrm hnrm hRU hR
  obtain ⟨-, -, hdual, -, hint, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hcj : ∀ {x}, x ∈ L.O → L.cj x ∈ L.O := fun hx => GlobalTheory.UnramOrder.cj_mem L hx
  have hO : ∀ c : 𝒪[F], algebraMap F E c ∈ L.O := fun c => (hint c).2 c.2
  have hq0 : 0 < resQ ϖ := by omega
  have hq0' : (0 : ℝ) < resQ ϖ := by exact_mod_cast hq0

  let p : ℕ → L.O := fun k => ⟨algebraMap F E ((ϖ : F) ^ k), hO (ϖ ^ k)⟩
  have hp : ∀ k, (Ideal.span {p k}).toAddSubgroup.index = resQ ϖ ^ (2 * k) := fun k => by
    have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ k)} = {p k} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff, p]
    rw [← hcard k, hset]
    rfl
  let π' : L.O := ⟨π, hπ⟩
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hπu : IsUnit π := by
    have := (IsUnit.mk0 _ (pow_ne_zero j hϖ0)).map (algebraMap F E)
    rw [← hππ] at this
    exact isUnit_of_mul_isUnit_left this
  have hreg : ∀ z, π' * z = 0 → z = 0 := fun z hz =>
    Subtype.ext (hπu.mul_right_eq_zero.1 (congrArg Subtype.val hz))
  have hπi : (Ideal.span {π'}).toAddSubgroup.index = resQ ϖ ^ j := by
    let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => hcj hx
    have h1 := index_span_mul π' (c π') hreg
    have h2 : π' * c π' = p j := Subtype.ext hππ
    rw [index_span_involution c (fun x => Subtype.ext (L.cj_cj x)), h2, hp, ← sq,
      mul_comm 2 j, pow_mul] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm

  let P : AddSubgroup (Fin n → E) :=
    U.toAddSubgroup.map (DistribSMul.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ N)))
  have hP : ∀ u, u ∈ P ↔ ∃ y ∈ U, u = algebraMap F E ((ϖ : F) ^ N) • y := fun u =>
    ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩
  have hPA : ∀ x : E, (∃ c ∈ L.O, algebraMap F E ((ϖ : F) ^ N) = x * c) →
      P ≤ divBy L Hm U e x := by
    rintro x ⟨c, hc, hx⟩ u hu
    obtain ⟨y, hy, rfl⟩ := (hP u).1 hu
    refine ⟨U.smul_mem (p N) hy, fun a => ⟨c * hf L Hm y (e a), L.O.mul_mem hc (hU y hy _ (he a)), ?_⟩⟩
    rw [form_smul_left, hx, mul_assoc]
  let M := divBy L Hm U e π
  have hPM : P ≤ M := hPA π hN
  have hMU : M ≤ U.toAddSubgroup := fun u hu => hu.1
  have hMi : M.relIndex U.toAddSubgroup = (resQ ϖ ^ j) ^ ρ := by
    rw [← hπi]
    exact relIndex_divBy L Hm U hU e he hee π'
  set R₀ := R.filter fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c with hR₀
  have hR₀M : ∀ u ∈ R₀, u ∈ M := fun u hu =>
    ⟨hRU u (Finset.mem_filter.1 hu).1, (Finset.mem_filter.1 hu).2⟩
  have hR' : ∀ u ∈ U.toAddSubgroup, ∃! w, w ∈ R ∧ u - w ∈ P := fun u hu => by
    simpa only [hP] using hR u hu
  have hR₀' : ∀ u ∈ M, ∃! w, w ∈ R₀ ∧ u - w ∈ P := fun u hu => by
    obtain ⟨w, ⟨hw, hw'⟩, huniq⟩ := hR' u hu.1
    have hwM : w ∈ M := by simpa using M.sub_mem hu (hPM hw')
    exact ⟨w, ⟨Finset.mem_filter.2 ⟨hw, hwM.2⟩, hw'⟩,
      fun y hy => huniq y ⟨(Finset.mem_filter.1 hy.1).1, hy.2⟩⟩
  have hshare : (R₀.card : ℝ) = (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) := by
    have h1 := AddSubgroup.relIndex_mul_relIndex P M U.toAddSubgroup hPM hMU
    rw [hMi, ← card_reps_eq_relIndex M P R₀ hR₀M hR₀',
      ← card_reps_eq_relIndex U.toAddSubgroup P R hRU hR', ← pow_mul] at h1
    rw [zpow_neg, ← div_eq_mul_inv, eq_div_iff (by positivity)]
    exact_mod_cast h1
  refine ⟨hshare, fun i hiN t u₀ ht => ?_⟩
  rw [← hshare]
  set k := i - j with hk
  let Q := divBy L Hm U e (π * algebraMap F E ((ϖ : F) ^ k))
  have hQM : Q ≤ M := fun u hu => ⟨hu.1, fun a => by
    obtain ⟨c, hc, h⟩ := hu.2 a
    exact ⟨_, L.O.mul_mem (p k).2 hc, by rw [h, mul_assoc]⟩⟩
  have hQi : Q.relIndex M = (resQ ϖ ^ (k * ρ)) ^ 2 := by
    have h1 := AddSubgroup.relIndex_mul_relIndex Q M U.toAddSubgroup hQM hMU
    have h2 : Q.relIndex U.toAddSubgroup = _ := relIndex_divBy L Hm U hU e he hee (π' * p k)
    rw [hMi, h2, index_span_mul π' _ hreg, hp, hπi, mul_pow] at h1
    rw [Nat.eq_of_mul_eq_mul_right (by positivity) h1]
    ring
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hiN
  have hPQ : P ≤ Q := by
    refine hPA _ ?_
    rcases le_total i j with hij | hij
    · have : k = 0 := by omega
      simpa only [this, pow_zero, map_one, mul_one] using hN
    · refine ⟨L.cj π * algebraMap F E ((ϖ : F) ^ m), L.O.mul_mem (hcj hπ) (p m).2, ?_⟩
      have : N = j + k + m := by omega
      rw [this, pow_add, pow_add, map_mul, map_mul, ← hππ]
      ring
  have hτ : algebraMap F E t * algebraMap F E ((ϖ : F) ^ i)
      = algebraMap F E ((u₀ : 𝒪[F]) : F) := by rw [← map_mul, ht]
  have key := sq_norm_sum_mul_relIndex_le M P Q hPQ R₀ hR₀M hR₀' (fun u => ψ (t * nrm u))
    (fun u => hψ1 _) ?_ ?_
  · rw [hQi, Nat.cast_pow, ← mul_pow] at key
    have h := (sq_le_sq₀ (by positivity) (by positivity)).1 key
    rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact_mod_cast h
  · intro u hu y' hy'
    obtain ⟨y, hy, rfl⟩ := (hP y').1 hy'
    have h2 : algebraMap F E t * algebraMap F E ((ϖ : F) ^ N) ∈ L.O := by
      rw [hm, pow_add, map_mul, ← mul_assoc, hτ]
      exact L.O.mul_mem (hO _) (p m).2
    have h3 : t * (nrm (u + algebraMap F E ((ϖ : F) ^ N) • y) - nrm u) ∈ 𝒪[F] := by
      rw [← hint, map_mul, map_sub, hnrm, hnrm]
      have : algebraMap F E t * (hf L Hm (u + algebraMap F E ((ϖ : F) ^ N) • y)
            (u + algebraMap F E ((ϖ : F) ^ N) • y) - hf L Hm u u)
          = algebraMap F E t * algebraMap F E ((ϖ : F) ^ N) * (hf L Hm u y + hf L Hm y u
            + algebraMap F E ((ϖ : F) ^ N) * hf L Hm y y) := by
        simp only [form_add_left, form_add_right, form_smul_left, form_smul_right,
          AlgEquiv.commutes]
        ring
      rw [this]
      exact L.O.mul_mem h2 (L.O.add_mem (L.O.add_mem (hU _ hu.1 _ hy) (hU _ hy _ hu.1))
        (L.O.mul_mem (p N).2 (hU _ hy _ hy)))
    have h4 := (hψ _).2 h3 1
    have h5 : t * nrm (u + algebraMap F E ((ϖ : F) ^ N) • y) = t * nrm u
        + t * (nrm (u + algebraMap F E ((ϖ : F) ^ N) • y) - nrm u) * ((1 : 𝒪[F]) : F) := by
      push_cast; ring
    show ψ _ = ψ _
    rw [h5, AddChar.map_add_eq_mul, h4, mul_one]
  · intro h hM hh
    obtain ⟨a, ha⟩ := not_forall.1 fun h' => hh ⟨hM.1, h'⟩
    obtain ⟨c, hc, hca⟩ := hM.2 a
    have hij : i = j + k := by
      by_contra hne
      have : k = 0 := by omega
      exact ha ⟨c, hc, by rw [this, pow_zero, map_one, mul_one, hca]⟩
    set z := algebraMap F E (t * (ϖ : F) ^ j) * c with hz
    have h1 : z ∉ L.O := fun h' => ha
      ⟨algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * z, L.O.mul_mem (hO _) h', by
          have h2 : algebraMap F E ((u₀ : 𝒪[F]) : F)
              * algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) = 1 := by
            rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
          rw [hij, pow_add, map_mul] at hτ
          rw [hca, hz, map_mul]
          linear_combination (-(π * c)) * h2
            - algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (π * c) * hτ⟩
    obtain ⟨b, hb⟩ := not_forall.1 fun h' => h1 (hdual _ h')
    obtain ⟨hb, hb'⟩ := Classical.not_imp.1 hb
    obtain ⟨s, hs⟩ := (L.cj_fix (z * L.cj b + L.cj (z * L.cj b))).1
      (by rw [map_add, L.cj_cj, add_comm])
    have hs' : s ∉ 𝒪[F] := fun h' => hb' ⟨⟨s, h'⟩, hs.symm⟩
    obtain ⟨y, hy⟩ := not_forall.1 fun h' => hs' ((hψ s).1 h')
    have hyb : algebraMap F E y * b ∈ L.O := L.O.mul_mem (hO y) hb
    let v : Fin n → E := (π * (algebraMap F E y * b)) • e a
    have hv : v ∈ M := by
      refine ⟨U.smul_mem (⟨_, L.O.mul_mem hπ hyb⟩ : L.O) (he a), fun a' =>
        ⟨algebraMap F E y * b * hf L Hm (e a) (e a'), L.O.mul_mem hyb (hU _ (he a) _ (he a')), ?_⟩⟩
      rw [form_smul_left, mul_assoc]
    refine ⟨v, hv, ψ (s * y), hy, fun u _ => ?_⟩
    have h2 : t * nrm (u + v + h) - t * nrm (u + v)
        = s * y + (t * nrm (u + h) - t * nrm u) := by
      apply hinj
      have hca' : hf L Hm (e a) h = L.cj π * L.cj c := by
        rw [← form_cj L Hm hH.1, hca, map_mul]
      have h3 : hf L Hm v h + hf L Hm h v = algebraMap F E ((ϖ : F) ^ j)
          * (algebraMap F E y * (b * L.cj c + c * L.cj b)) := by
        simp only [v, form_smul_left, form_smul_right, hca, hca', map_mul, AlgEquiv.commutes,
          ← hππ]
        ring
      simp only [hz, map_mul, AlgEquiv.commutes, L.cj_cj] at hs
      simp only [map_sub, map_add (algebraMap F E), map_mul, hnrm, hs, form_add_left,
        form_add_right]
      linear_combination algebraMap F E t * h3
    show ψ _ * conj (ψ _) = _ * (ψ _ * conj (ψ _))
    rw [GaussSum.mul_conj_eq ψ hψ1, GaussSum.mul_conj_eq ψ hψ1, h2, AddChar.map_add_eq_mul]

end GlobalTheory.HL.DivisibleGauss
