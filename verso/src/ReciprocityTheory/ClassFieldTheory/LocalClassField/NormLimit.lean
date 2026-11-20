import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.PairKEqZeroOfMemNormGrp
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function
open scoped commutatorElement

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

/- English proof (translation)
Establish `hK : FiniteDimensional ℚ_[p] K` using `finDim_of_le p hL h`. Take `⟨E, hKE, hE, hEU⟩` from `exists_subG_eq_of_isOpen hK (subG p K L ⊔ commutator (GK p K)) (Subgroup.isOpen_mono le_sup_left (isOpen_subG hL))`. Use `⟨E, ⟨hKE, hE, hEU ▸ le_sup_right⟩, ?_, hEU⟩` and prove the remaining obligations. Use `(subG_le_iff (L := E) (L' := L) hKE).1 (hEU ▸ le_sup_left)` as an intermediate fact. Rewrite `this` using `[sup_eq_right.2 h]`. Then use the resulting hypothesis.
-/
theorem exists_maxAb (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal] :
    ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K E ∧ E ≤ L ∧ subG p K E = subG p K L ⊔ commutator (GK p K) := by
  have hK : FiniteDimensional ℚ_[p] K := finDim_of_le p hL h
  obtain ⟨E, hKE, hE, hEU⟩ := exists_subG_eq_of_isOpen hK (subG p K L ⊔ commutator (GK p K))
    (Subgroup.isOpen_mono le_sup_left (isOpen_subG hL))
  refine ⟨E, ⟨hKE, hE, hEU ▸ le_sup_right⟩, ?_, hEU⟩
  have := (subG_le_iff (L := E) (L' := L) hKE).1 (hEU ▸ le_sup_left)
  rwa [sup_eq_right.2 h] at this

section grp

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (s : G)

include hH in

/- English proof (translation)
Establish `hc : ∀ a ∈ H, s * a * s⁻¹ ∈ H` using `fun a ha => Subgroup.Normal.conj_mem inferInstance a ha s`. Use `⟨{ carrier := {x | ∃ h ∈ H, x = s * h * s⁻¹ * h⁻¹} one_mem' := ⟨1, H.one_mem, by group⟩ mul_mem' := ?_ inv_mem' := ?_ }, fun x => Iff.rfl⟩` and prove the remaining obligations. Introduce and unpack `_ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩`. Use `⟨a * b, H.mul_mem ha hb, ?_⟩` and prove the remaining obligations. Establish `h1` using `hH a⁻¹ (H.inv_mem ha) (s * b * s⁻¹ * b⁻¹) (H.mul_mem (hc b hb) (H.inv_mem hb))`.

Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Use `⟨a⁻¹, H.inv_mem ha, ?_⟩` and prove the remaining obligations. Establish `h1` using `hH a ha (s * a⁻¹ * s⁻¹) (hc _ (H.inv_mem ha))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_twist_subgroup_nl : ∃ I : Subgroup G, ∀ x, x ∈ I ↔ ∃ h ∈ H, x = s * h * s⁻¹ * h⁻¹ := by
  have hc : ∀ a ∈ H, s * a * s⁻¹ ∈ H := fun a ha => Subgroup.Normal.conj_mem inferInstance a ha s
  refine ⟨{ carrier := {x | ∃ h ∈ H, x = s * h * s⁻¹ * h⁻¹}
            one_mem' := ⟨1, H.one_mem, by group⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a * b, H.mul_mem ha hb, ?_⟩
    have h1 := hH a⁻¹ (H.inv_mem ha) (s * b * s⁻¹ * b⁻¹) (H.mul_mem (hc b hb) (H.inv_mem hb))
    calc s * a * s⁻¹ * a⁻¹ * (s * b * s⁻¹ * b⁻¹) = s * a * s⁻¹ * (a⁻¹ * (s * b * s⁻¹ * b⁻¹)) := by group
      _ = s * a * s⁻¹ * ((s * b * s⁻¹ * b⁻¹) * a⁻¹) := by rw [h1]
      _ = _ := by group
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, H.inv_mem ha, ?_⟩
    have h1 := hH a ha (s * a⁻¹ * s⁻¹) (hc _ (H.inv_mem ha))
    calc (s * a * s⁻¹ * a⁻¹)⁻¹ = a * (s * a⁻¹ * s⁻¹) := by group
      _ = _ := by rw [h1]; group

end grp

/- English proof (translation)
Take `⟨I, hI⟩` from `exists_twist_subgroup_nl H hH s`. Rewrite using `[← hI]`. Establish `hc : ∀ (g : G), ∀ a ∈ H, g * a * g⁻¹ ∈ H` using `fun g a ha => Subgroup.Normal.conj_mem inferInstance a ha g`. Establish `key : ∀ (i : ℤ), ∀ h ∈ H, s ^ i * h * (s ^ i)⁻¹ * h⁻¹ ∈ I`. Introduce `i`.

Proceed by induction on `i using Int.induction_on with`. Consider the case `zero => intro h _`. Simplify using the standard rewrite rules. Consider the case `succ i ih`. Introduce `h hh`.

Establish `h1 : s * (s ^ (i : ℤ) * h * (s ^ (i : ℤ))⁻¹) * s⁻¹ * (s ^ (i : ℤ) * h * (s ^ (i : ℤ))⁻¹)⁻¹ ∈ I` using `(hI _).2 ⟨_, hc _ h hh, rfl⟩`. Use `I.mul_mem h1 (ih h hh)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[zpow_add_one]`. Establish `: s ^ (i : ℤ) * s = s * s ^ (i : ℤ)` using `by rw [← zpow_add_one, ← zpow_one_add, add_comm]`.

Rewrite using `[this]`. Use `group`. Consider the case `pred i ih`. Introduce `h hh`. Establish `h1 : s * (s ^ (-(i : ℤ) - 1) * h * (s ^ (-(i : ℤ) - 1))⁻¹) * s⁻¹ * (s ^ (-(i : ℤ) - 1) * h * (s ^ (-(i : ℤ) - 1))⁻¹)⁻¹ ∈ I` using `(hI _).2 ⟨_, hc _ h hh, rfl⟩`.

Use `I.mul_mem (I.inv_mem h1) (ih h hh)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Establish `e : s ^ (-(i : ℤ)) = s * s ^ (-(i : ℤ) - 1)` using `by rw [← zpow_one_add]; congr 1; ring`. Rewrite using `[e]`. Use `group`.

Establish `hle : commutator G ≤ I`. Rewrite using `[commutator_def, Subgroup.commutator_le]`. Introduce `a _ b _`. Take `⟨i, hi⟩` from `hs a`. Take `⟨j, hj⟩` from `hs b`.

Use `set u := a * s ^ i with hu`. Use `set v := b * s ^ j with hv`. Establish `ea : a = u * s ^ (-i)` using `by rw [hu, zpow_neg]; group`. Establish `eb : b = v * s ^ (-j)` using `by rw [hv, zpow_neg]; group`. Establish `k1` using `key (-i) v hj`.

Establish `k2` using `I.inv_mem (key (-j) u hi)`. Use `I.mul_mem k1 k2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Establish `c1` using `hH u hi (s ^ (-i) * v * (s ^ (-i))⁻¹ * (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) * v⁻¹) (H.mul_mem (H.mul_mem (hc _ v hj) (hc _ _ (H.inv_mem hi))) (H.inv_mem hj))`. Establish `c2` using `hH (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) (hc _ _ (H.inv_mem hi)) (v⁻¹ * u) (H.mul_mem (H.inv_mem hj) hi)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[commutatorElement_def, ea, eb]`. Use `group`. Use `_ = (s ^ (-i) * v * (s ^ (-i))⁻¹ * (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) * v⁻¹) * u := c1`. Use `_ = s ^ (-i) * v * (s ^ (-i))⁻¹ * ((s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) * (v⁻¹ * u)) := by group`.

Use `_ = s ^ (-i) * v * (s ^ (-i))⁻¹ * ((v⁻¹ * u) * (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹)) := by rw [c2]`. Use `_ = _ := by group`. Conclude with `hle hx`.
-/
theorem exists_of_mem_commutator {G : Type*} [Group G] (H : Subgroup G) [H.Normal] (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (s : G) (hs : ∀ g : G, ∃ (k : ℤ), g * s ^ k ∈ H) (x : G) (hx : x ∈ commutator G) :
    ∃ h ∈ H, x = s * h * s⁻¹ * h⁻¹ := by
  obtain ⟨I, hI⟩ := exists_twist_subgroup_nl H hH s
  rw [← hI]
  have hc : ∀ (g : G), ∀ a ∈ H, g * a * g⁻¹ ∈ H := fun g a ha => Subgroup.Normal.conj_mem inferInstance a ha g
  have key : ∀ (i : ℤ), ∀ h ∈ H, s ^ i * h * (s ^ i)⁻¹ * h⁻¹ ∈ I := by
    intro i
    induction i using Int.induction_on with
    | zero => intro h _; simp
    | succ i ih =>
      intro h hh
      have h1 : s * (s ^ (i : ℤ) * h * (s ^ (i : ℤ))⁻¹) * s⁻¹ * (s ^ (i : ℤ) * h * (s ^ (i : ℤ))⁻¹)⁻¹ ∈ I :=
        (hI _).2 ⟨_, hc _ h hh, rfl⟩
      have := I.mul_mem h1 (ih h hh)
      convert this using 1
      rw [zpow_add_one]
      have : s ^ (i : ℤ) * s = s * s ^ (i : ℤ) := by rw [← zpow_add_one, ← zpow_one_add, add_comm]
      rw [this]
      group
    | pred i ih =>
      intro h hh
      have h1 : s * (s ^ (-(i : ℤ) - 1) * h * (s ^ (-(i : ℤ) - 1))⁻¹) * s⁻¹ *
          (s ^ (-(i : ℤ) - 1) * h * (s ^ (-(i : ℤ) - 1))⁻¹)⁻¹ ∈ I :=
        (hI _).2 ⟨_, hc _ h hh, rfl⟩
      have := I.mul_mem (I.inv_mem h1) (ih h hh)
      convert this using 1
      have e : s ^ (-(i : ℤ)) = s * s ^ (-(i : ℤ) - 1) := by rw [← zpow_one_add]; congr 1; ring
      rw [e]
      group
  have hle : commutator G ≤ I := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨i, hi⟩ := hs a
    obtain ⟨j, hj⟩ := hs b
    set u := a * s ^ i with hu
    set v := b * s ^ j with hv
    have ea : a = u * s ^ (-i) := by rw [hu, zpow_neg]; group
    have eb : b = v * s ^ (-j) := by rw [hv, zpow_neg]; group
    have k1 := key (-i) v hj
    have k2 := I.inv_mem (key (-j) u hi)
    have := I.mul_mem k1 k2
    convert this using 1
    have c1 := hH u hi (s ^ (-i) * v * (s ^ (-i))⁻¹ * (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) * v⁻¹)
      (H.mul_mem (H.mul_mem (hc _ v hj) (hc _ _ (H.inv_mem hi))) (H.inv_mem hj))
    have c2 := hH (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) (hc _ _ (H.inv_mem hi)) (v⁻¹ * u) (H.mul_mem (H.inv_mem hj) hi)
    calc ⁅a, b⁆ = u * (s ^ (-i) * v * (s ^ (-i))⁻¹ * (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) * v⁻¹) := by
          rw [commutatorElement_def, ea, eb]; group
      _ = (s ^ (-i) * v * (s ^ (-i))⁻¹ * (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) * v⁻¹) * u := c1
      _ = s ^ (-i) * v * (s ^ (-i))⁻¹ * ((s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) * (v⁻¹ * u)) := by group
      _ = s ^ (-i) * v * (s ^ (-i))⁻¹ * ((v⁻¹ * u) * (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹)) := by rw [c2]
      _ = _ := by group
  exact hle hx

/- English proof (translation)
Establish `hne : (⟨((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p), hx⟩ : K) ≠ 0` using `fun h => (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h)`. Use `⟨Units.mk0 _ hne, ?_⟩` and prove the remaining obligations. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Both sides reduce to the same expression.
-/
theorem exists_ofK_eq_nl (x : KbarMult p) (hx : x ∈ multOf p K) : ∃ a : Kˣ, ofK p K (Additive.ofMul a) = x := by
  have hne : (⟨((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p), hx⟩ : K) ≠ 0 := fun h =>
    (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h)
  refine ⟨Units.mk0 _ hne, ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  rfl

/- English proof (translation)
Establish `: Finite (GK p K ⧸ subG p K L)` using `finite_GalLK hL`. Use `Fintype.ofFinite (GK p K ⧸ subG p K L)` as an intermediate fact. Rewrite using `[normHom_apply, normHom_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[← kbarRep_mul, ← kbarRep_out y hy (c.out * σ)]`. Use `congr 3`. Rewrite using `[QuotientGroup.mk_mul, QuotientGroup.out_eq']`. Both sides reduce to the same expression. Use `_ = _ := Equiv.sum_comp _ (fun c : GalLK p K L => kbarRep p K c.out y)`.
-/
theorem normHom_kbarRep_nl (hL : FiniteDimensional ℚ_[p] L) [(subG p K L).Normal] (σ : GK p K) (y : KbarMult p)
    (hy : y ∈ multOf p L) : normHom p K L (kbarRep p K σ y) = normHom p K L y := by
  have : Finite (GK p K ⧸ subG p K L) := finite_GalLK hL
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  rw [normHom_apply, normHom_apply]
  calc ∑ c : GK p K ⧸ subG p K L, kbarRep p K c.out (kbarRep p K σ y)
      = ∑ c : GalLK p K L, kbarRep p K ((Equiv.mulRight (QuotientGroup.mk σ : GalLK p K L)) c).out y := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← kbarRep_mul, ← kbarRep_out y hy (c.out * σ)]
        congr 3
        rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
        rfl
    _ = _ := Equiv.sum_comp _ (fun c : GalLK p K L => kbarRep p K c.out y)

/- English proof (translation)
Introduce `a ha`. Take `⟨y, hy, hya⟩` from `(mem_normGrp_iff p K L a).1 ha`. Take `⟨b, hb⟩` from `exists_ofK_eq_nl _ (normHom_mem hL hML y hy)`. Take `⟨y', hy', hyb⟩` from `(mem_normGrp_iff p M L' b).1 (h ((mem_normGrp_iff p M L b).2 ⟨y, hy, hb.symm⟩))`. Use `(mem_normGrp_iff p K L' a).2 ⟨y', hy', ?_⟩` and prove the remaining obligations.

Rewrite using `[← normHom_trans hL' hKM hML' y' hy', hyb, hb, normHom_trans hL hKM hML y hy, hya]`.
-/
theorem normGrp_le_of_tower_nl {M L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : FiniteDimensional ℚ_[p] L)
    (hL' : FiniteDimensional ℚ_[p] L') (hKM : K ≤ M) (hML : M ≤ L) (hML' : M ≤ L')
    (h : normGrp p M L ≤ normGrp p M L') : normGrp p K L ≤ normGrp p K L' := by
  intro a ha
  obtain ⟨y, hy, hya⟩ := (mem_normGrp_iff p K L a).1 ha
  obtain ⟨b, hb⟩ := exists_ofK_eq_nl _ (normHom_mem hL hML y hy)
  obtain ⟨y', hy', hyb⟩ := (mem_normGrp_iff p M L' b).1 (h ((mem_normGrp_iff p M L b).2 ⟨y, hy, hb.symm⟩))
  refine (mem_normGrp_iff p K L' a).2 ⟨y', hy', ?_⟩
  rw [← normHom_trans hL' hKM hML' y' hy', hyb, hb, normHom_trans hL hKM hML y hy, hya]

/- English proof (translation)
Rewrite using `[← comap_resGK_subG h L, Subgroup.map_comap_eq, range_resGK, inf_eq_right]`. Conclude with `subG_anti h'`.
-/
theorem map_resGK_subG_nl {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ M) (h' : M ≤ L) :
    (subG p M L).map (resGK h) = subG p K L := by
  rw [← comap_resGK_subG h L, Subgroup.map_comap_eq, range_resGK, inf_eq_right]
  exact subG_anti h'

/- English proof (translation)
Set `π : GK p K →* GalLK p K L` to `QuotientGroup.mk' (subG p K L)`. Establish `hπ : Surjective π` using `QuotientGroup.mk'_surjective _`. Set `H : Subgroup (GalLK p K L)` to `(subG p K M).map π`. Establish `: H.Normal` using `Subgroup.Normal.map inferInstance π hπ`. Establish `hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a`.

Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩`. Rewrite `ha`, `hb` using `[SetLike.mem_coe, ← range_resGK hKM]`. Take `⟨a, rfl⟩` from `ha`. Take `⟨b, rfl⟩` from `hb`. Establish `h1 : ⁅a, b⁆ ∈ subG p M L` using `hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))`.

Establish `h2 : ⁅resGK hKM a, resGK hKM b⁆ ∈ subG p K L`. Rewrite using `[← map_commutatorElement]`. Conclude with `h1`. Establish `h3 : π ⁅resGK hKM a, resGK hKM b⁆ = 1` using `(QuotientGroup.eq_one_iff _).2 h2`. Rewrite `h3` using `[map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]`.

Conclude with `h3`. Establish `hs : ∀ x : GalLK p K L, ∃ k : ℤ, x * (π σ) ^ k ∈ H`. Introduce `x`. Take `⟨x, rfl⟩` from `hπ x`. Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.1 (hσ (QuotientGroup.mk x))`.

Use `⟨-k, x * σ ^ (-k), ?_, by rw [map_mul, map_zpow]⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, ← hk, zpow_neg, mul_inv_cancel]`. Establish `hx : π g ∈ commutator (GalLK p K L)`. Establish `h1 : π g ∈ (subG p K L ⊔ commutator (GK p K)).map π` using `Subgroup.mem_map_of_mem _ hg`. Establish `e : (subG p K L).map π = ⊥` using `(Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' _).ge`.

Rewrite `h1` using `[Subgroup.map_sup, e, bot_sup_eq, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 hπ, ← commutator_def]`. Then use the resulting hypothesis. Take `⟨_, ⟨h0, hh0, rfl⟩, hx'⟩` from `exists_of_mem_commutator H hH (π σ) hs (π g) hx`. Rewrite `hh0` using `[SetLike.mem_coe, ← range_resGK hKM]`. Take `⟨h', rfl⟩` from `hh0`. Use `⟨h', ?_⟩` and prove the remaining obligations.

Rewrite using `[← QuotientGroup.eq]`. Conclude with `hx'`.
-/
theorem exists_twist_nl {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKM : K ≤ M) [(subG p K M).Normal]
    [(subG p K L).Normal] (σ : GK p K)
    (hσ : ∀ g : GalLK p K M, g ∈ Subgroup.zpowers (QuotientGroup.mk σ : GalLK p K M))
    (hcomm : commutator (GK p M) ≤ subG p M L) (g : GK p K) (hg : g ∈ subG p K L ⊔ commutator (GK p K)) :
    ∃ h' : GK p M, g⁻¹ * (σ * resGK hKM h' * σ⁻¹ * (resGK hKM h')⁻¹) ∈ subG p K L := by
  let π : GK p K →* GalLK p K L := QuotientGroup.mk' (subG p K L)
  have hπ : Surjective π := QuotientGroup.mk'_surjective _
  let H : Subgroup (GalLK p K L) := (subG p K M).map π
  have : H.Normal := Subgroup.Normal.map inferInstance π hπ
  have hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [SetLike.mem_coe, ← range_resGK hKM] at ha hb
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    have h1 : ⁅a, b⁆ ∈ subG p M L :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have h2 : ⁅resGK hKM a, resGK hKM b⁆ ∈ subG p K L := by
      rw [← map_commutatorElement]; exact h1
    have h3 : π ⁅resGK hKM a, resGK hKM b⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h2
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  have hs : ∀ x : GalLK p K L, ∃ k : ℤ, x * (π σ) ^ k ∈ H := by
    intro x
    obtain ⟨x, rfl⟩ := hπ x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hσ (QuotientGroup.mk x))
    refine ⟨-k, x * σ ^ (-k), ?_, by rw [map_mul, map_zpow]⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, ← hk, zpow_neg,
      mul_inv_cancel]
  have hx : π g ∈ commutator (GalLK p K L) := by
    have h1 : π g ∈ (subG p K L ⊔ commutator (GK p K)).map π := Subgroup.mem_map_of_mem _ hg
    have e : (subG p K L).map π = ⊥ := (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' _).ge
    rwa [Subgroup.map_sup, e, bot_sup_eq, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 hπ, ← commutator_def] at h1
  obtain ⟨_, ⟨h0, hh0, rfl⟩, hx'⟩ := exists_of_mem_commutator H hH (π σ) hs (π g) hx
  rw [SetLike.mem_coe, ← range_resGK hKM] at hh0
  obtain ⟨h', rfl⟩ := hh0
  refine ⟨h', ?_⟩
  rw [← QuotientGroup.eq]
  exact hx'

/- English proof (translation)
Establish `hLf` using `hL.fin`. Establish `hML` using `hL.le`. Establish `hKL` using `hKM.trans hML`. Establish `hM : FiniteDimensional ℚ_[p] M` using `finDim_of_le p hLf hML`. Use `le_antisymm (normGrp_anti hLf hE.le hEL) fun a ha => ?_` and prove the remaining obligations.

Establish `hMab : IsAbLK p K M` using `isAbLK_of_cyclic hM hKM _ hσ`. Establish `hME : M ≤ E`. Use `(subG_le_iff (L := M) (L' := E) hKM).1 (by rw [hE']; exact sup_le (subG_anti hML) hMab.comm)` as an intermediate fact. Rewrite `this` using `[sup_eq_right.2 hE.le]`. Then use the resulting hypothesis. Establish `hEab : IsAbLK p M E` using `hL.of_le hME hEL`.

Take `⟨y, hy, hya⟩` from `(mem_normGrp_iff p K E a).1 ha`. Take `⟨b, hb⟩` from `exists_ofK_eq_nl _ (normHom_mem hE.fin hME y hy)`. Establish `hbN : b ∈ normGrp p M E` using `(mem_normGrp_iff p M E b).2 ⟨y, hy, hb.symm⟩`. Establish `hba : normHom p K M (ofK p M (Additive.ofMul b)) = ofK p K (Additive.ofMul a)`. Rewrite using `[hb, normHom_trans hE.fin hKM hME y hy, hya]`.

Take `⟨g, hg⟩` from `exists_isRecip hL b`. Establish `hgE : g ∈ subG p M E` using `((hg.of_le hEL).mem_subG_iff hM hEab).2 hbN`. Establish `hgE' : resGK hKM g ∈ subG p K L ⊔ commutator (GK p K)`. Rewrite using `[← hE']`. Conclude with `hgE`.

Take `⟨h', hh'⟩` from `exists_twist_nl hKM σ hσ hL.comm _ hgE'`. Take `⟨c, hc⟩` from `exists_isRecip_of_gal hM hL h'`. Establish `stM` using `(subG_normal_iff hKM).1 inferInstance`. Establish `stL` using `(subG_normal_iff hKL).1 inferInstance`. Establish `hσc : kbarRep p K σ (ofK p M (Additive.ofMul c)) ∈ multOf p M` using `stM σ _ (ofK_mem p M _)`.

Take `⟨c', hc'⟩` from `exists_ofK_eq_nl _ hσc`. Choose the witnesses or unpack the hypotheses as in `⟨g', hg'⟩ : ∃ g' : GK p M, resGK hKM g' = σ * resGK hKM h' * σ⁻¹ := by`. Establish `: σ * resGK hKM h' * σ⁻¹ ∈ (resGK hKM).range`. Rewrite using `[range_resGK]`. Conclude with `Subgroup.Normal.conj_mem inferInstance _ (by rw [← range_resGK hKM]; exact ⟨_, rfl⟩) σ`.

Conclude with `this`. Establish `hc'' : IsRecip p M L c' g'` using `IsRecip.conj hK hM hKM σ (stM σ) (stL σ) (stL σ⁻¹) (b := c) (b' := c') (congrArg (fun z : KbarMult p => ((Additive.toMul z : (PadicAlgCl p)ˣ) : PadicAlgCl p)) hc') hg' hc`. Establish `hd : IsRecip p M L (b⁻¹ * (c' * c⁻¹)) (g⁻¹ * (g' * h'⁻¹))` using `hg.inv.mul (hc''.mul hc.inv)`. Establish `hdm : g⁻¹ * (g' * h'⁻¹) ∈ subG p M L`. Rewrite using `[← comap_resGK_subG hKM L, Subgroup.mem_comap]`.

Simplify using `only [map_mul, map_inv, hg']`. Conclude with `hh'`. Take `⟨l, hl, hld⟩` from `(mem_normGrp_iff p M L _).1 ((hd.mem_subG_iff hM hL).1 hdm)`. Use `(mem_normGrp_iff p K L a).2 ⟨-l, neg_mem hl, ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, ← normHom_trans hLf hKM hML l hl, hld, ofMul_mul, ofMul_mul, ofMul_inv, ofMul_inv, map_add, map_add, map_neg, map_neg, map_add, map_add, map_neg, map_neg, hc', normHom_kbarRep_nl hM σ _ (ofK_mem p M _), hba]`.

Normalize the expressions using the abelian group laws.
-/
theorem normGrp_eq_of_cyclic_of_ab (hK : FiniteDimensional ℚ_[p] K) {M E : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKM : K ≤ M) [(subG p K M).Normal] (σ : GK p K)
    (hσ : ∀ g : GalLK p K M, g ∈ Subgroup.zpowers (QuotientGroup.mk σ : GalLK p K M)) (hL : IsAbLK p M L)
    [(subG p K L).Normal] (hE : IsAbLK p K E) (hEL : E ≤ L)
    (hE' : subG p K E = subG p K L ⊔ commutator (GK p K)) : normGrp p K L = normGrp p K E := by
  have hLf := hL.fin
  have hML := hL.le
  have hKL := hKM.trans hML
  have hM : FiniteDimensional ℚ_[p] M := finDim_of_le p hLf hML
  refine le_antisymm (normGrp_anti hLf hE.le hEL) fun a ha => ?_
  have hMab : IsAbLK p K M := isAbLK_of_cyclic hM hKM _ hσ
  have hME : M ≤ E := by
    have := (subG_le_iff (L := M) (L' := E) hKM).1 (by rw [hE']; exact sup_le (subG_anti hML) hMab.comm)
    rwa [sup_eq_right.2 hE.le] at this
  have hEab : IsAbLK p M E := hL.of_le hME hEL
  obtain ⟨y, hy, hya⟩ := (mem_normGrp_iff p K E a).1 ha
  obtain ⟨b, hb⟩ := exists_ofK_eq_nl _ (normHom_mem hE.fin hME y hy)
  have hbN : b ∈ normGrp p M E := (mem_normGrp_iff p M E b).2 ⟨y, hy, hb.symm⟩
  have hba : normHom p K M (ofK p M (Additive.ofMul b)) = ofK p K (Additive.ofMul a) := by
    rw [hb, normHom_trans hE.fin hKM hME y hy, hya]
  obtain ⟨g, hg⟩ := exists_isRecip hL b
  have hgE : g ∈ subG p M E := ((hg.of_le hEL).mem_subG_iff hM hEab).2 hbN
  have hgE' : resGK hKM g ∈ subG p K L ⊔ commutator (GK p K) := by
    rw [← hE']; exact hgE
  obtain ⟨h', hh'⟩ := exists_twist_nl hKM σ hσ hL.comm _ hgE'
  obtain ⟨c, hc⟩ := exists_isRecip_of_gal hM hL h'
  have stM := (subG_normal_iff hKM).1 inferInstance
  have stL := (subG_normal_iff hKL).1 inferInstance
  have hσc : kbarRep p K σ (ofK p M (Additive.ofMul c)) ∈ multOf p M := stM σ _ (ofK_mem p M _)
  obtain ⟨c', hc'⟩ := exists_ofK_eq_nl _ hσc
  obtain ⟨g', hg'⟩ : ∃ g' : GK p M, resGK hKM g' = σ * resGK hKM h' * σ⁻¹ := by
    have : σ * resGK hKM h' * σ⁻¹ ∈ (resGK hKM).range := by
      rw [range_resGK]
      exact Subgroup.Normal.conj_mem inferInstance _ (by rw [← range_resGK hKM]; exact ⟨_, rfl⟩) σ
    exact this
  have hc'' : IsRecip p M L c' g' := IsRecip.conj hK hM hKM σ (stM σ) (stL σ) (stL σ⁻¹) (b := c) (b' := c')
    (congrArg (fun z : KbarMult p => ((Additive.toMul z : (PadicAlgCl p)ˣ) : PadicAlgCl p)) hc') hg' hc
  have hd : IsRecip p M L (b⁻¹ * (c' * c⁻¹)) (g⁻¹ * (g' * h'⁻¹)) := hg.inv.mul (hc''.mul hc.inv)
  have hdm : g⁻¹ * (g' * h'⁻¹) ∈ subG p M L := by
    rw [← comap_resGK_subG hKM L, Subgroup.mem_comap]
    simp only [map_mul, map_inv, hg']
    exact hh'
  obtain ⟨l, hl, hld⟩ := (mem_normGrp_iff p M L _).1 ((hd.mem_subG_iff hM hL).1 hdm)
  refine (mem_normGrp_iff p K L a).2 ⟨-l, neg_mem hl, ?_⟩
  rw [map_neg, ← normHom_trans hLf hKM hML l hl, hld, ofMul_mul, ofMul_mul, ofMul_inv, ofMul_inv, map_add, map_add,
    map_neg, map_neg, map_add, map_add, map_neg, map_neg, hc', normHom_kbarRep_nl hM σ _ (ofK_mem p M _), hba]
  abel

/- English proof (translation)
Take `⟨H, hH, hle⟩` from `(eq_top_or_exists_le_coatom (commutator G)).resolve_left (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne`. Establish `hn : H.Normal` using `⟨fun n hn g => by`. Establish `h1 : ⁅g, n⁆ ∈ H` using `hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))`. Establish `h2` using `H.mul_mem h1 hn`. Rewrite using `[commutatorElement_def, inv_mul_cancel_right] at h2⟩` and apply the resulting hypothesis.

Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, s ∉ H := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hH.1 (eq_top_iff.2 fun x _ => hc x)`. Use `⟨H, s, hn, hH.1, ?_⟩` and prove the remaining obligations.

Set `V : Subgroup G` to `(Subgroup.zpowers (QuotientGroup.mk s : G ⧸ H)).comap (QuotientGroup.mk' H)`. Establish `hlt : H < V`. Use `lt_of_le_of_ne (fun x hx => ?_) fun h => hs (h ▸ (Subgroup.mem_zpowers _ : _ ∈ Subgroup.zpowers (QuotientGroup.mk s : G ⧸ H)))` and prove the remaining obligations. Use `show (QuotientGroup.mk x : G ⧸ H) ∈ Subgroup.zpowers (QuotientGroup.mk s : G ⧸ H)`. Rewrite using `[(QuotientGroup.eq_one_iff x).2 hx]`.

Conclude with `Subgroup.one_mem _`. Establish `hV : V = ⊤` using `hH.2 V hlt`. Introduce `g`. Establish `hg : g ∈ V` using `hV ▸ Subgroup.mem_top g`. Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.1 (show (QuotientGroup.mk g : G ⧸ H) ∈ Subgroup.zpowers (QuotientGroup.mk s : G ⧸ H) from hg)`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientGroup.eq, QuotientGroup.mk_zpow, hk]`.
-/
theorem exists_cyclic_quotient_nl {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] [Nontrivial G] :
    ∃ (H : Subgroup G) (s : G), H.Normal ∧ H ≠ ⊤ ∧ ∀ g : G, ∃ k : ℤ, (s ^ k)⁻¹ * g ∈ H := by
  obtain ⟨H, hH, hle⟩ := (eq_top_or_exists_le_coatom (commutator G)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne
  have hn : H.Normal := ⟨fun n hn g => by
    have h1 : ⁅g, n⁆ ∈ H := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have h2 := H.mul_mem h1 hn
    rwa [commutatorElement_def, inv_mul_cancel_right] at h2⟩
  obtain ⟨s, hs⟩ : ∃ s, s ∉ H := by
    by_contra hc
    push Not at hc
    exact hH.1 (eq_top_iff.2 fun x _ => hc x)
  refine ⟨H, s, hn, hH.1, ?_⟩
  let V : Subgroup G := (Subgroup.zpowers (QuotientGroup.mk s : G ⧸ H)).comap (QuotientGroup.mk' H)
  have hlt : H < V := by
    refine lt_of_le_of_ne (fun x hx => ?_) fun h => hs (h ▸ (Subgroup.mem_zpowers _ : _ ∈ Subgroup.zpowers (QuotientGroup.mk s : G ⧸ H)))
    show (QuotientGroup.mk x : G ⧸ H) ∈ Subgroup.zpowers (QuotientGroup.mk s : G ⧸ H)
    rw [(QuotientGroup.eq_one_iff x).2 hx]
    exact Subgroup.one_mem _
  have hV : V = ⊤ := hH.2 V hlt
  intro g
  have hg : g ∈ V := hV ▸ Subgroup.mem_top g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (show (QuotientGroup.mk g : G ⧸ H) ∈ Subgroup.zpowers (QuotientGroup.mk s : G ⧸ H) from hg)
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hk]

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `K L hK hL h _ hsol E hE hEL hE' hn`. Establish `: Finite (GalLK p K L)` using `finite_GalLK hL`. Break down `subsingleton_or_nontrivial (GalLK p K L) with hss | hnt` into its components or cases.

Establish `htop : subG p K L = ⊤` using `QuotientGroup.subgroup_eq_top_of_subsingleton _ hss`. Establish `hLab : IsAbLK p K L` using `⟨h, hL, by rw [htop]; exact le_top⟩`. Establish `: (subG p K K).Normal` using `(isAbLK_self hK).normal`. Establish `hσ : ∀ g : GalLK p K K, g ∈ Subgroup.zpowers (QuotientGroup.mk (1 : GK p K) : GalLK p K K)`. Introduce `g`.

Proceed by induction on `g using QuotientGroup.induction_on with`. Consider the case `H g`. Rewrite using `[(QuotientGroup.eq_one_iff g).2 (show g ∈ subG p K K from fun x hx => g.commutes ⟨x, hx⟩)]`. Conclude with `Subgroup.one_mem _`. Conclude with `normGrp_eq_of_cyclic_of_ab hK (le_refl K) 1 hσ hLab hE hEL hE'`.

Take `⟨H, s, hHn, hHtop, hs⟩` from `exists_cyclic_quotient_nl (G := GalLK p K L)`. Take `⟨σ, rfl⟩` from `QuotientGroup.mk_surjective s`. Set `π : GK p K →* GalLK p K L` to `QuotientGroup.mk' (subG p K L)`. Establish `hπ : Surjective π` using `QuotientGroup.mk'_surjective _`. Establish `hUle : subG p K L ≤ H.comap π` using `fun x hx => by`.

Rewrite using `[Subgroup.mem_comap, show π x = 1 from (QuotientGroup.eq_one_iff x).2 hx]`. Conclude with `H.one_mem`. Take `⟨M, hKM, hM, hMU⟩` from `exists_subG_eq_of_isOpen hK (H.comap π) (Subgroup.isOpen_mono hUle (isOpen_subG hL))`. Establish `hML : M ≤ L`. Use `(subG_le_iff (L := M) (L' := L) hKM).1 (hMU ▸ hUle)` as an intermediate fact.

Rewrite `this` using `[sup_eq_right.2 h]`. Then use the resulting hypothesis. Establish `hMn : (subG p K M).Normal` using `hMU ▸ hHn.comap π`. Establish `hσ : ∀ g : GalLK p K M, g ∈ Subgroup.zpowers (QuotientGroup.mk σ : GalLK p K M)`. Introduce `g`. Proceed by induction on `g using QuotientGroup.induction_on with`.

Consider the case `H g`. Take `⟨k, hk⟩` from `hs (π g)`. Use `Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientGroup.mk_zpow, QuotientGroup.eq, hMU, Subgroup.mem_comap, map_mul, map_inv, map_zpow]`. Conclude with `hk`.

Establish `hlt : degLK p M L < n`. Establish `h1` using `degLK_mul hKM hML`. Establish `h2 : degLK p K M ≠ 1`. Unfold `degLK`. Rewrite using `[hMU, Subgroup.index_comap_of_surjective _ hπ]`.

Conclude with `fun h => hHtop (Subgroup.index_eq_one.1 h)`. Establish `h3` using `degLK_pos (K := K) hM`. Establish `h4` using `degLK_pos (K := M) hL`. Rewrite using `[← hn, h1]`. Conclude with `lt_mul_of_one_lt_left h4 (by omega)`.

Establish `hMLn : (subG p M L).Normal` using `subG_normal_of_le hKM h inferInstance`. Establish `hsolM : Group.IsSolvable (GalLK p M L)`. Set `f : GalLK p M L →* GalLK p K L` to `QuotientGroup.map _ _ (resGK hKM) (comap_resGK_subG hKM L).ge`. Establish `hf : Injective f`. Rewrite using `[injective_iff_map_eq_one]`.

Introduce `x`. Proceed by induction on `x using QuotientGroup.induction_on with`. Consider the case `H z`. Introduce `hx`. Conclude with `(QuotientGroup.eq_one_iff _).2 ((QuotientGroup.eq_one_iff (resGK hKM z)).1 hx)`.

Conclude with `Group.isSolvable_of_isSolvable_injective hf`. Take `⟨E', hE'ab, hE'L, hE'U⟩` from `exists_maxAb (K := M) hL hML`. Establish `e1 : normGrp p M L = normGrp p M E'` using `ih _ hlt M L hM hL hML hsolM E' hE'ab hE'L hE'U rfl`. Establish `hME'` using `hE'ab.le`. Establish `e2 : normGrp p K L = normGrp p K E'` using `le_antisymm (normGrp_le_of_tower_nl hL hE'ab.fin hKM hML hME' e1.le) (normGrp_le_of_tower_nl hE'ab.fin hL hKM hME' hML e1.ge)`.

Establish `e3 : subG p K E' = subG p K L ⊔ ⁅subG p K M, subG p K M⁆`. Rewrite using `[← map_resGK_subG_nl hKM hME', hE'U, Subgroup.map_sup, map_resGK_subG_nl hKM hML, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_resGK]`. Establish `hE'n : (subG p K E').Normal` using `by rw [e3]; infer_instance`. Establish `e4 : subG p K E = subG p K E' ⊔ commutator (GK p K)`. Rewrite using `[hE', e3, sup_assoc, commutator_def, sup_eq_right.2 (Subgroup.commutator_mono le_top le_top)]`.

Establish `hEE' : E ≤ E'`. Use `(subG_le_iff (L := E) (L' := E') hE.le).1 (e4 ▸ le_sup_left)` as an intermediate fact. Rewrite `this` using `[sup_eq_right.2 (hKM.trans hME')]`. Then use the resulting hypothesis. Rewrite using `[e2]`. Conclude with `normGrp_eq_of_cyclic_of_ab hK hKM σ hσ hE'ab hE hEE' e4`.
-/
theorem normGrp_eq_of_soluble_nl (n : ℕ) : ∀ (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
    (_ : FiniteDimensional ℚ_[p] K) (_ : FiniteDimensional ℚ_[p] L) (_ : K ≤ L) [(subG p K L).Normal]
    (_ : Group.IsSolvable (GalLK p K L)) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : IsAbLK p K E) (_ : E ≤ L)
    (_ : subG p K E = subG p K L ⊔ commutator (GK p K)), degLK p K L = n → normGrp p K L = normGrp p K E := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L hK hL h _ hsol E hE hEL hE' hn
  have : Finite (GalLK p K L) := finite_GalLK hL
  rcases subsingleton_or_nontrivial (GalLK p K L) with hss | hnt
  · have htop : subG p K L = ⊤ := QuotientGroup.subgroup_eq_top_of_subsingleton _ hss
    have hLab : IsAbLK p K L := ⟨h, hL, by rw [htop]; exact le_top⟩
    have : (subG p K K).Normal := (isAbLK_self hK).normal
    have hσ : ∀ g : GalLK p K K, g ∈ Subgroup.zpowers (QuotientGroup.mk (1 : GK p K) : GalLK p K K) := by
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [(QuotientGroup.eq_one_iff g).2 (show g ∈ subG p K K from fun x hx => g.commutes ⟨x, hx⟩)]
        exact Subgroup.one_mem _
    exact normGrp_eq_of_cyclic_of_ab hK (le_refl K) 1 hσ hLab hE hEL hE'
  · obtain ⟨H, s, hHn, hHtop, hs⟩ := exists_cyclic_quotient_nl (G := GalLK p K L)
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective s
    let π : GK p K →* GalLK p K L := QuotientGroup.mk' (subG p K L)
    have hπ : Surjective π := QuotientGroup.mk'_surjective _
    have hUle : subG p K L ≤ H.comap π := fun x hx => by
      rw [Subgroup.mem_comap, show π x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
      exact H.one_mem
    obtain ⟨M, hKM, hM, hMU⟩ := exists_subG_eq_of_isOpen hK (H.comap π)
      (Subgroup.isOpen_mono hUle (isOpen_subG hL))
    have hML : M ≤ L := by
      have := (subG_le_iff (L := M) (L' := L) hKM).1 (hMU ▸ hUle)
      rwa [sup_eq_right.2 h] at this
    have hMn : (subG p K M).Normal := hMU ▸ hHn.comap π
    have hσ : ∀ g : GalLK p K M, g ∈ Subgroup.zpowers (QuotientGroup.mk σ : GalLK p K M) := by
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨k, hk⟩ := hs (π g)
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
        rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, hMU, Subgroup.mem_comap, map_mul, map_inv, map_zpow]
        exact hk
    have hlt : degLK p M L < n := by
      have h1 := degLK_mul hKM hML
      have h2 : degLK p K M ≠ 1 := by
        unfold degLK
        rw [hMU, Subgroup.index_comap_of_surjective _ hπ]
        exact fun h => hHtop (Subgroup.index_eq_one.1 h)
      have h3 := degLK_pos (K := K) hM
      have h4 := degLK_pos (K := M) hL
      rw [← hn, h1]
      exact lt_mul_of_one_lt_left h4 (by omega)
    have hMLn : (subG p M L).Normal := subG_normal_of_le hKM h inferInstance
    have hsolM : Group.IsSolvable (GalLK p M L) := by
      let f : GalLK p M L →* GalLK p K L := QuotientGroup.map _ _ (resGK hKM) (comap_resGK_subG hKM L).ge
      have hf : Injective f := by
        rw [injective_iff_map_eq_one]
        intro x
        induction x using QuotientGroup.induction_on with
        | H z =>
          intro hx
          exact (QuotientGroup.eq_one_iff _).2 ((QuotientGroup.eq_one_iff (resGK hKM z)).1 hx)
      exact Group.isSolvable_of_isSolvable_injective hf
    obtain ⟨E', hE'ab, hE'L, hE'U⟩ := exists_maxAb (K := M) hL hML
    have e1 : normGrp p M L = normGrp p M E' := ih _ hlt M L hM hL hML hsolM E' hE'ab hE'L hE'U rfl
    have hME' := hE'ab.le
    have e2 : normGrp p K L = normGrp p K E' :=
      le_antisymm (normGrp_le_of_tower_nl hL hE'ab.fin hKM hML hME' e1.le)
        (normGrp_le_of_tower_nl hE'ab.fin hL hKM hME' hML e1.ge)
    have e3 : subG p K E' = subG p K L ⊔ ⁅subG p K M, subG p K M⁆ := by
      rw [← map_resGK_subG_nl hKM hME', hE'U, Subgroup.map_sup, map_resGK_subG_nl hKM hML, commutator_def,
        Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_resGK]
    have hE'n : (subG p K E').Normal := by rw [e3]; infer_instance
    have e4 : subG p K E = subG p K E' ⊔ commutator (GK p K) := by
      rw [hE', e3, sup_assoc, commutator_def, sup_eq_right.2 (Subgroup.commutator_mono le_top le_top)]
    have hEE' : E ≤ E' := by
      have := (subG_le_iff (L := E) (L' := E') hE.le).1 (e4 ▸ le_sup_left)
      rwa [sup_eq_right.2 (hKM.trans hME')] at this
    rw [e2]
    exact normGrp_eq_of_cyclic_of_ab hK hKM σ hσ hE'ab hE hEE' e4

/- English proof (translation)
The claim follows from `normGrp_eq_of_soluble_nl _ K L hK hL h hsol E hE hEL hE' rfl`.
-/
theorem normGrp_eq_of_soluble (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal]
    (hsol : Group.IsSolvable (GalLK p K L)) {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (hE : IsAbLK p K E) (hEL : E ≤ L)
    (hE' : subG p K E = subG p K L ⊔ commutator (GK p K)) : normGrp p K L = normGrp p K E :=
  normGrp_eq_of_soluble_nl _ K L hK hL h hsol E hE hEL hE' rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
