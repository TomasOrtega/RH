import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.IsoCyclic
import GroundTheory.LocalFields.AbstractLocalReciprocity.FunctorialityTransfer

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

section Normal

variable {G : Type*} [Group G]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun n hn g => by rw [Subgroup.mem_subgroupOf] at hn ⊢ have h := hN.conj_mem ⟨n, hMK n.2⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, hMK g.2⟩ rw [Subgroup.mem_subgroupOf] at h simpa using h⟩`.
-/
theorem normal_subgroupOf_of_le {K L M : Subgroup G} (hMK : M ≤ K) [hN : (L.subgroupOf K).Normal] :
    (L.subgroupOf M).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hN.conj_mem ⟨n, hMK n.2⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, hMK g.2⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h⟩

/- English proof (translation)
The claim follows from `(Subgroup.index_eq_card _).symm`.
-/
theorem card_quotient_eq_relIndex (K L : Subgroup G) :
    Nat.card (K ⧸ L.subgroupOf K) = L.relIndex K :=
  (Subgroup.index_eq_card _).symm

end Normal

section FixedField

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

def fixedOpen (H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G where
  toSubgroup := (H.comap (QuotientGroup.mk' _)).map (K : Subgroup G).subtype
  isOpen' := Subgroup.isOpen_mono (H₁ := (L : Subgroup G)) (fun x hx => ⟨⟨x, hLK hx⟩, by
      show ((⟨x, hLK hx⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈ H
      rw [(QuotientGroup.eq_one_iff (⟨x, hLK hx⟩ : (K : Subgroup G))).2 (Subgroup.mem_subgroupOf.2 hx)]
      exact H.one_mem, rfl⟩) L.isOpen

/- English proof (translation)
Use `show g ∈ (H.comap (QuotientGroup.mk' _)).map (K : Subgroup G).subtype ↔ _`. Rewrite using `[Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨k.2, hk⟩`.

Introduce and unpack `⟨h, hH⟩`. Conclude with `⟨⟨g, h⟩, hH, rfl⟩`.
-/
theorem mem_fixedOpen {H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)} {g : G} :
    g ∈ ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ↔
      ∃ h : g ∈ (K : Subgroup G), ((⟨g, h⟩ : (K : Subgroup G)) :
        (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈ H := by
  show g ∈ (H.comap (QuotientGroup.mk' _)).map (K : Subgroup G).subtype ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨h, hH⟩
    exact ⟨⟨g, h⟩, hH, rfl⟩

variable (H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))

/- English proof (translation)
Introduce `x hx` and use `(mem_fixedOpen hLK).2 ⟨hLK hx, by rw [(QuotientGroup.eq_one_iff (⟨x, hLK hx⟩ : (K : Subgroup G))).2 (Subgroup.mem_subgroupOf.2 hx)] exact H.one_mem⟩`.
-/
theorem le_fixedOpen : L ≤ fixedOpen hLK H := fun x hx =>
  (mem_fixedOpen hLK).2 ⟨hLK hx, by
    rw [(QuotientGroup.eq_one_iff (⟨x, hLK hx⟩ : (K : Subgroup G))).2 (Subgroup.mem_subgroupOf.2 hx)]
    exact H.one_mem⟩

/- English proof (translation)
Introduce `_ hx` and use `((mem_fixedOpen hLK).1 hx).1`.
-/
theorem fixedOpen_le : fixedOpen hLK H ≤ K := fun _ hx => ((mem_fixedOpen hLK).1 hx).1

instance normal_fixedOpen_self :
    ((L : Subgroup G).subgroupOf ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G)).Normal :=
  normal_subgroupOf_of_le (K := (K : Subgroup G)) (fun _ hx => ((mem_fixedOpen hLK).1 hx).1)

instance normal_fixedOpen [hH : H.Normal] :
    (((fixedOpen hLK H : OpenSubgroup G) : Subgroup G).subgroupOf K).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨_, hnH⟩ := (mem_fixedOpen hLK).1 hn
    refine (mem_fixedOpen hLK).2 ⟨(g * n * g⁻¹).2, ?_⟩
    exact hH.conj_mem _ hnH (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)⟩

/- English proof (translation)
Use extensionality with `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H k`. Rewrite using `[mk_mem_range_galRestrict_iff (le_fixedOpen hLK H) (fixedOpen_le hLK H), mem_fixedOpen]`. Conclude with `⟨fun ⟨_, h⟩ => h, fun h => ⟨k.2, h⟩⟩`.
-/
theorem range_galRestrict_fixedOpen [CompactSpace G] :
    (galRestrict (K := K) (L := L) (K' := fixedOpen hLK H) (L' := L) (fixedOpen_le hLK H)
      le_rfl).range = H := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [mk_mem_range_galRestrict_iff (le_fixedOpen hLK H) (fixedOpen_le hLK H), mem_fixedOpen]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨k.2, h⟩⟩

noncomputable def galFixedEquiv [CompactSpace G] :
    ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ⧸
      (L : Subgroup G).subgroupOf ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ≃* H :=
  (MonoidHom.ofInjective (galRestrict_injective (K := K) (L := L) (fixedOpen_le hLK H))).trans
    (MulEquiv.subgroupCongr (range_galRestrict_fixedOpen hLK H))

/- English proof (translation)
Rewrite using `[← card_quotient_eq_relIndex]`. Conclude with `Nat.card_congr (galFixedEquiv hLK H).toEquiv`.
-/
theorem relIndex_fixedOpen [CompactSpace G] :
    (L : Subgroup G).relIndex (fixedOpen hLK H) = Nat.card H := by
  rw [← card_quotient_eq_relIndex]
  exact Nat.card_congr (galFixedEquiv hLK H).toEquiv

/- English proof (translation)
Establish `h1` using `Subgroup.relIndex_mul_relIndex (H := (L : Subgroup G)) (K := ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G)) (L := (K : Subgroup G)) (fun x hx => le_fixedOpen hLK H hx) (fun x hx => fixedOpen_le hLK H hx)`. Rewrite `h1` using `[relIndex_fixedOpen, ← card_quotient_eq_relIndex (K : Subgroup G) (L : Subgroup G), ← H.card_mul_index]`. Conclude with `Nat.eq_of_mul_eq_mul_left Nat.card_pos h1`.
-/
theorem relIndex_fixedOpen_eq_index [CompactSpace G] :
    ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G).relIndex K = H.index := by
  have h1 := Subgroup.relIndex_mul_relIndex (H := (L : Subgroup G))
    (K := ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G)) (L := (K : Subgroup G))
    (fun x hx => le_fixedOpen hLK H hx) (fun x hx => fixedOpen_le hLK H hx)
  rw [relIndex_fixedOpen, ← card_quotient_eq_relIndex (K : Subgroup G) (L : Subgroup G),
    ← H.card_mul_index] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

end FixedField

section Restrict

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

omit [IsTopologicalGroup G] [CompactSpace G] in

/- English proof (translation)
Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H τ => exact ⟨(τ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K), rfl⟩`.
-/
theorem galRestrict_surjective {K L M : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((M : Subgroup G).subgroupOf K).Normal] (hLM : L ≤ M) :
    Function.Surjective (galRestrict (K := K) (L := M) (K' := K) (L' := L) le_rfl hLM) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H τ => exact ⟨(τ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K), rfl⟩

omit [CompactSpace G] in

/- English proof (translation)
Establish `h` using `map_conj_eq_of_normal (L := (M : Subgroup G)) (fun _ hy => hMK hy) hg`. Apply `OpenSubgroup.ext` to reduce the goal to its premises. Introduce `x`. Use `show x ∈ ((conjOpen g M : OpenSubgroup G) : Subgroup G) ↔ x ∈ (M : Subgroup G)`. Rewrite using `[coe_conjOpen, h]`.
-/
theorem conjOpen_eq_of_normal {K M : OpenSubgroup G} (hMK : M ≤ K)
    [((M : Subgroup G).subgroupOf K).Normal] {g : G} (hg : g ∈ (K : Subgroup G)) :
    conjOpen g M = M := by
  have h := map_conj_eq_of_normal (L := (M : Subgroup G)) (fun _ hy => hMK hy) hg
  apply OpenSubgroup.ext
  intro x
  show x ∈ ((conjOpen g M : OpenSubgroup G) : Subgroup G) ↔ x ∈ (M : Subgroup G)
  rw [coe_conjOpen, h]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_one]`. Introduce `z hz`. Proceed by induction on `z using QuotientGroup.induction_on with`. Consider the case `H q`. Establish `hq : Abelianization.lift f (Abelianization.of q) = 1` using `hz`.

Rewrite `hq` using `[Abelianization.lift_apply_of]`. Use `h hq` as an intermediate fact. Rewrite `this` using `[← Abelianization.ker_of, MonoidHom.mem_ker]`. Conclude with `this`.
-/
theorem Abelianization.lift_injective_of_ker_le {Γ T : Type*} [Group Γ] [CommGroup T] (f : Γ →* T)
    (h : f.ker ≤ commutator Γ) : Function.Injective (Abelianization.lift f) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  induction z using QuotientGroup.induction_on with
  | H q =>
    have hq : Abelianization.lift f (Abelianization.of q) = 1 := hz
    rw [Abelianization.lift_apply_of] at hq
    have := h hq
    rw [← Abelianization.ker_of, MonoidHom.mem_ker] at this
    exact this

end Restrict

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

/- English proof (translation)
Substitute `hK hL` using the available equality. Conclude with `h`.
-/
theorem reciprocity_congr {K₁ K₂ L₁ L₂ : OpenSubgroup G} (hK : K₁ = K₂) (hL : L₁ = L₂)
    (h1 : L₁ ≤ K₁) (h2 : L₂ ≤ K₂) [((L₁ : Subgroup G).subgroupOf K₁).Normal]
    [((L₂ : Subgroup G).subgroupOf K₂).Normal] {τ : G} (hτ1 : τ ∈ (K₁ : Subgroup G))
    (hτ2 : τ ∈ (K₂ : Subgroup G)) {a : A} (ha1 : a ∈ fixedModule A (K₁ : Subgroup G))
    (ha2 : a ∈ fixedModule A (K₂ : Subgroup G))
    (h : D.reciprocity h1 hax ((⟨τ, hτ1⟩ : (K₁ : Subgroup G)) :
        (K₁ : Subgroup G) ⧸ (L₁ : Subgroup G).subgroupOf K₁) =
      ((⟨a, ha1⟩ : fixedModule A (K₁ : Subgroup G)) : tateZero A (K₁ : Subgroup G) (L₁ : Subgroup G))) :
    D.reciprocity h2 hax ((⟨τ, hτ2⟩ : (K₂ : Subgroup G)) :
        (K₂ : Subgroup G) ⧸ (L₂ : Subgroup G).subgroupOf K₂) =
      ((⟨a, ha2⟩ : fixedModule A (K₂ : Subgroup G)) : tateZero A (K₂ : Subgroup G) (L₂ : Subgroup G)) := by
  subst hK hL
  exact h

section Tower

variable {K M L : OpenSubgroup G} (hLM : L ≤ M) (hMK : M ≤ K)
  [((L : Subgroup G).subgroupOf K).Normal] [((L : Subgroup G).subgroupOf M).Normal]
  [((M : Subgroup G).subgroupOf K).Normal]

/- English proof (translation)
Establish `hLK : L ≤ K` using `hLM.trans hMK`. Introduce `x`. Proceed by induction on `x using QuotientGroup.induction_on with`. Consider the case `H a`. Take `⟨q', hq'⟩` from `h2 (a : tateZero A (K : Subgroup G) (M : Subgroup G))`.

Take `⟨q, rfl⟩` from `galRestrict_surjective (K := K) hLM q'`. Establish `e1` using `D.reciprocity_galRestrict hax hMK hLK le_rfl hLM q`. Take `⟨c, hc⟩` from `QuotientGroup.mk_surjective (D.reciprocity hLK hax q)`. Rewrite `e1` using `[hq', ← hc, normTateZero_mk, norm_self, MonoidHom.id_apply, QuotientGroup.eq]`. Take `⟨b, hb⟩` from `e1`.

Take `⟨p, hp⟩` from `h1 ((b⁻¹ : fixedModule A (M : Subgroup G)) : tateZero A (M : Subgroup G) (L : Subgroup G))`. Establish `e2` using `D.reciprocity_galRestrict hax hLK hLM hMK le_rfl p`. Use `⟨q * galRestrict hMK le_rfl p, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, e2, hp, ← hc, normTateZero_mk, map_inv, hb, ← QuotientGroup.mk_mul]`. Use `congr 1`.

Use `group`.
-/
theorem reciprocity_surjective_of_tower (h1 : Function.Surjective (D.reciprocity hLM hax))
    (h2 : Function.Surjective (D.reciprocity hMK hax)) :
    Function.Surjective (D.reciprocity (hLM.trans hMK) hax) := by
  have hLK : L ≤ K := hLM.trans hMK
  intro x
  induction x using QuotientGroup.induction_on with
  | H a =>
    obtain ⟨q', hq'⟩ := h2 (a : tateZero A (K : Subgroup G) (M : Subgroup G))
    obtain ⟨q, rfl⟩ := galRestrict_surjective (K := K) hLM q'
    have e1 := D.reciprocity_galRestrict hax hMK hLK le_rfl hLM q
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (D.reciprocity hLK hax q)
    rw [hq', ← hc, normTateZero_mk, norm_self, MonoidHom.id_apply, QuotientGroup.eq] at e1
    obtain ⟨b, hb⟩ := e1
    obtain ⟨p, hp⟩ := h1 ((b⁻¹ : fixedModule A (M : Subgroup G)) :
      tateZero A (M : Subgroup G) (L : Subgroup G))
    have e2 := D.reciprocity_galRestrict hax hLK hLM hMK le_rfl p
    refine ⟨q * galRestrict hMK le_rfl p, ?_⟩
    rw [map_mul, e2, hp, ← hc, normTateZero_mk, map_inv, hb, ← QuotientGroup.mk_mul]
    congr 1
    group

/- English proof (translation)
Establish `hLK : L ≤ K` using `hLM.trans hMK`. Establish `hMK' : (M : Subgroup G) ≤ K` using `fun _ hx => hMK hx`. Establish `hLM' : (L : Subgroup G) ≤ M` using `fun _ hx => hLM hx`. Establish `hLK' : (L : Subgroup G) ≤ K` using `fun _ hx => hLK hx`. Use `set ι := galRestrict (K := K) (L := L) (K' := M) (L' := L) hMK le_rfl with hι`.

Use `set S := (commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)).comap ι with hS`. Establish `hconj : ∀ (g : G) (hg : g ∈ (K : Subgroup G)) (τ : G) (hτ : τ ∈ (M : Subgroup G)) (x : A) (hx : x ∈ fixedModule A (M : Subgroup G)), D.reciprocity hLM hax ((⟨τ, hτ⟩ : (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) = ((⟨x, hx⟩ : fixedModule A (M : Subgroup G …`. Introduce `g hg τ hτ x hx h`. Establish `e` using `D.reciprocity_galConj hax g hLM ((⟨τ, hτ⟩ : (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M)`. Rewrite `e` using `[galConj_mk, h, tateZeroConj_mk]`.

Conclude with `D.reciprocity_congr hax (conjOpen_eq_of_normal hMK hg) (conjOpen_eq_of_normal hLK hg) (conjOpen_mono g hLM) hLM _ _ (a := g • x) _ _ e`. Introduce `q hq`. Rewrite `hq` using `[MonoidHom.mem_ker]`. Establish `hq1 : galRestrict (K` using `K) (L := M) (K' := K) (L' := L) le_rfl hLM q = 1 := by`. Apply `(reciprocity_bijective_of_isCyclic (D := D) hMK hax hcyc).1` to reduce the goal to its premises.

Rewrite using `[map_one, D.reciprocity_galRestrict hax hMK hLK le_rfl hLM q, hq, map_one]`. Take `⟨k, rfl⟩` from `QuotientGroup.mk_surjective q`. Rewrite `hq1` using `[galRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]`. Use `set t : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M := ((⟨k, hq1⟩ : (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) with ht`. Establish `hιt : ι t = QuotientGroup.mk k` using `rfl`.

Rewrite `hq`, the goal using `[← hιt]`. Establish `h2` using `D.reciprocity_galRestrict hax hLK hLM hMK le_rfl t`. Rewrite `h2` using `[hq]`. Take `⟨a, ha⟩` from `QuotientGroup.mk_surjective (D.reciprocity hLM hax t)`. Rewrite `h2` using `[← ha, normTateZero_mk]`.

Take `⟨b, hb⟩` from `(QuotientGroup.eq_one_iff _).1 h2.symm`. Use `set a' : fixedModule A (M : Subgroup G) := a * (norm A (M : Subgroup G) (L : Subgroup G) b)⁻¹ with ha'def`. Establish `ha' : norm A (K : Subgroup G) (M : Subgroup G) a' = 1`. Rewrite using `[ha'def, map_mul, map_inv, norm_norm hLM' hMK' b, hb, mul_inv_cancel]`. Establish `hmk : (QuotientGroup.mk a' : tateZero A (M : Subgroup G) (L : Subgroup G)) = D.reciprocity hLM hax t`.

Rewrite using `[← ha, QuotientGroup.eq]`. Conclude with `⟨b, by rw [ha'def]; group⟩`. Establish `hsub : Subsingleton (tateNegOne A (K : Subgroup G) (M : Subgroup G))` using `(Nat.card_eq_one_iff_unique.1 (hax K M hMK hcyc).2).1`. Establish `haug : (a' : A) ∈ augmentation A (K : Subgroup G) (M : Subgroup G)`. Establish `h0 : ((⟨a', ha'⟩ : (norm A (K : Subgroup G) (M : Subgroup G)).ker) : tateNegOne A (K : Subgroup G) (M : Subgroup G)) = 1` using `Subsingleton.elim _ _`.

Conclude with `(QuotientGroup.eq_one_iff (⟨a', ha'⟩ : (norm A (K : Subgroup G) (M : Subgroup G)).ker)).1 h0`. Use `set P : Subgroup A := ((S.map (D.reciprocity hLM hax)).comap (QuotientGroup.mk' (norm A (M : Subgroup G) (L : Subgroup G)).range)).map (fixedModule A (M : Subgroup G)).subtype with hP`. Establish `hAP : augmentation A (K : Subgroup G) (M : Subgroup G) ≤ P`. Rewrite using `[augmentation, Subgroup.closure_le]`. Introduce and unpack `_ ⟨g, hg, x, hx, rfl⟩`.

Take `⟨ρ, hρ⟩` from `hs ((⟨x, hx⟩ : fixedModule A (M : Subgroup G)) : tateZero A (M : Subgroup G) (L : Subgroup G))`. Take `⟨τ, rfl⟩` from `QuotientGroup.mk_surjective ρ`. Establish `e` using `hconj g hg τ τ.2 x hx hρ`. Use `⟨⟨g • x / x, (fixedModule A (M : Subgroup G)).div_mem (smul_mem_fixedModule_of_normal hMK' hg hx) hx⟩, ?_, rfl⟩` and prove the remaining obligations. Use `⟨((⟨g * τ * g⁻¹, conj_mem_of_normal hg (hMK' τ.2) τ.2⟩ : (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) * (τ : (M : Subgroup G) ⧸ _)⁻¹, ?_, ?_⟩` and prove the remaining obligations.

Use `show ι (_ * _) ∈ commutator _`. Rewrite using `[map_mul, map_inv]`. Establish `hc` using `Subgroup.commutator_mem_commutator (Subgroup.mem_top ((⟨g, hg⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) (Subgroup.mem_top ((⟨τ, hMK' τ.2⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))`. Rewrite `hc` using `[commutatorElement_def]`. Conclude with `hc`.

Rewrite using `[map_mul, map_inv, e, hρ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, QuotientGroup.mk'_apply]`. Use `congr 1`. Conclude with `Subtype.ext (div_eq_mul_inv _ _).symm`. Take `⟨y, hy, hya⟩` from `hAP haug`. Take `rfl : y = a'` from `Subtype.ext hya`.

Take `⟨s, hsS, hrs⟩` from `hy`. Rewrite `hrs` using `[QuotientGroup.mk'_apply, hmk]`. Establish `hts : t * s⁻¹ ∈ (D.reciprocity hLM hax).ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, hrs, mul_inv_cancel]`. Establish `hcomm : ι (t * s⁻¹) ∈ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)`.

Establish `h` using `hk hts`. Rewrite `h`, the goal using `[← Abelianization.ker_of, MonoidHom.mem_ker]`. Rewrite using `[← Abelianization.map_of, h, map_one]`. Establish `e3 : ι t = ι (t * s⁻¹) * ι s` using `by rw [map_mul, map_inv, inv_mul_cancel_right]`. Rewrite using `[e3]`.

Conclude with `Subgroup.mul_mem _ hcomm hsS`.
-/
theorem ker_reciprocity_le_of_tower
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (M : Subgroup G).subgroupOf K))
    (hs : Function.Surjective (D.reciprocity hLM hax))
    (hk : (D.reciprocity hLM hax).ker ≤ commutator ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M)) :
    (D.reciprocity (hLM.trans hMK) hax).ker ≤
      commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  have hLK : L ≤ K := hLM.trans hMK
  have hMK' : (M : Subgroup G) ≤ K := fun _ hx => hMK hx
  have hLM' : (L : Subgroup G) ≤ M := fun _ hx => hLM hx
  have hLK' : (L : Subgroup G) ≤ K := fun _ hx => hLK hx
  set ι := galRestrict (K := K) (L := L) (K' := M) (L' := L) hMK le_rfl with hι
  set S := (commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)).comap ι with hS

  have hconj : ∀ (g : G) (hg : g ∈ (K : Subgroup G)) (τ : G) (hτ : τ ∈ (M : Subgroup G)) (x : A)
      (hx : x ∈ fixedModule A (M : Subgroup G)),
      D.reciprocity hLM hax ((⟨τ, hτ⟩ : (M : Subgroup G)) :
          (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) =
        ((⟨x, hx⟩ : fixedModule A (M : Subgroup G)) :
          tateZero A (M : Subgroup G) (L : Subgroup G)) →
      D.reciprocity hLM hax ((⟨g * τ * g⁻¹, conj_mem_of_normal hg (hMK' hτ) hτ⟩ :
          (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) =
        ((⟨g • x, smul_mem_fixedModule_of_normal hMK' hg hx⟩ : fixedModule A (M : Subgroup G)) :
          tateZero A (M : Subgroup G) (L : Subgroup G)) := by
    intro g hg τ hτ x hx h
    have e := D.reciprocity_galConj hax g hLM
      ((⟨τ, hτ⟩ : (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M)
    rw [galConj_mk, h, tateZeroConj_mk] at e
    exact D.reciprocity_congr hax (conjOpen_eq_of_normal hMK hg) (conjOpen_eq_of_normal hLK hg)
      (conjOpen_mono g hLM) hLM _ _ (a := g • x) _ _ e
  intro q hq
  rw [MonoidHom.mem_ker] at hq

  have hq1 : galRestrict (K := K) (L := M) (K' := K) (L' := L) le_rfl hLM q = 1 := by
    apply (reciprocity_bijective_of_isCyclic (D := D) hMK hax hcyc).1
    rw [map_one, D.reciprocity_galRestrict hax hMK hLK le_rfl hLM q, hq, map_one]
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [galRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
  set t : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M :=
    ((⟨k, hq1⟩ : (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) with ht
  have hιt : ι t = QuotientGroup.mk k := rfl
  rw [← hιt] at hq ⊢

  have h2 := D.reciprocity_galRestrict hax hLK hLM hMK le_rfl t
  rw [hq] at h2
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (D.reciprocity hLM hax t)
  rw [← ha, normTateZero_mk] at h2
  obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff _).1 h2.symm
  set a' : fixedModule A (M : Subgroup G) := a * (norm A (M : Subgroup G) (L : Subgroup G) b)⁻¹
    with ha'def
  have ha' : norm A (K : Subgroup G) (M : Subgroup G) a' = 1 := by
    rw [ha'def, map_mul, map_inv, norm_norm hLM' hMK' b, hb, mul_inv_cancel]
  have hmk : (QuotientGroup.mk a' : tateZero A (M : Subgroup G) (L : Subgroup G)) =
      D.reciprocity hLM hax t := by
    rw [← ha, QuotientGroup.eq]
    exact ⟨b, by rw [ha'def]; group⟩

  have hsub : Subsingleton (tateNegOne A (K : Subgroup G) (M : Subgroup G)) :=
    (Nat.card_eq_one_iff_unique.1 (hax K M hMK hcyc).2).1
  have haug : (a' : A) ∈ augmentation A (K : Subgroup G) (M : Subgroup G) := by
    have h0 : ((⟨a', ha'⟩ : (norm A (K : Subgroup G) (M : Subgroup G)).ker) :
        tateNegOne A (K : Subgroup G) (M : Subgroup G)) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff
      (⟨a', ha'⟩ : (norm A (K : Subgroup G) (M : Subgroup G)).ker)).1 h0

  set P : Subgroup A := ((S.map (D.reciprocity hLM hax)).comap
    (QuotientGroup.mk' (norm A (M : Subgroup G) (L : Subgroup G)).range)).map
      (fixedModule A (M : Subgroup G)).subtype with hP
  have hAP : augmentation A (K : Subgroup G) (M : Subgroup G) ≤ P := by
    rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, x, hx, rfl⟩
    obtain ⟨ρ, hρ⟩ := hs ((⟨x, hx⟩ : fixedModule A (M : Subgroup G)) :
      tateZero A (M : Subgroup G) (L : Subgroup G))
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective ρ
    have e := hconj g hg τ τ.2 x hx hρ
    refine ⟨⟨g • x / x, (fixedModule A (M : Subgroup G)).div_mem
      (smul_mem_fixedModule_of_normal hMK' hg hx) hx⟩, ?_, rfl⟩
    refine ⟨((⟨g * τ * g⁻¹, conj_mem_of_normal hg (hMK' τ.2) τ.2⟩ : (M : Subgroup G)) :
      (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) * (τ : (M : Subgroup G) ⧸ _)⁻¹, ?_, ?_⟩
    · show ι (_ * _) ∈ commutator _
      rw [map_mul, map_inv]
      have hc := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top ((⟨g, hg⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
        (Subgroup.mem_top ((⟨τ, hMK' τ.2⟩ : (K : Subgroup G)) :
          (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
      rw [commutatorElement_def] at hc
      exact hc
    · rw [map_mul, map_inv, e, hρ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        QuotientGroup.mk'_apply]
      congr 1
      exact Subtype.ext (div_eq_mul_inv _ _).symm
  obtain ⟨y, hy, hya⟩ := hAP haug
  obtain rfl : y = a' := Subtype.ext hya
  obtain ⟨s, hsS, hrs⟩ := hy
  rw [QuotientGroup.mk'_apply, hmk] at hrs
  have hts : t * s⁻¹ ∈ (D.reciprocity hLM hax).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hrs, mul_inv_cancel]
  have hcomm : ι (t * s⁻¹) ∈ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
    have h := hk hts
    rw [← Abelianization.ker_of, MonoidHom.mem_ker] at h ⊢
    rw [← Abelianization.map_of, h, map_one]
  have e3 : ι t = ι (t * s⁻¹) * ι s := by rw [map_mul, map_inv, inv_mul_cancel_right]
  rw [e3]
  exact Subgroup.mul_mem _ hcomm hsS

end Tower

section PGroup

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `K L hLK _ hn hP`. Distinguish the cases in `hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)`. Establish `hb` using `reciprocity_bijective_of_isCyclic (D := D) hLK hax hcyc`.

Use `⟨hb.2, fun q hq => ?_⟩` and prove the remaining obligations. Rewrite using `[(injective_iff_map_eq_one _).1 hb.1 q hq]`. Conclude with `Subgroup.one_mem _`. Take `⟨k, hk⟩` from `hP.exists_card_eq`. Establish `hk0 : k ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hk` using `[pow_zero]`. Conclude with `hcyc (@isCyclic_of_subsingleton _ _ (Nat.card_eq_one_iff_unique.1 hk).1)`. Take `⟨H, hH⟩` from `Sylow.exists_subgroup_card_pow_prime p (pow_dvd_pow p (Nat.sub_le k 1) |>.trans hk.symm.dvd)`. Establish `hpk : p ^ (k - 1) * p = p ^ k` using `by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]`.

Establish `hHi : H.index = p`. Establish `h` using `H.card_mul_index`. Rewrite `h` using `[hH, hk, ← hpk]`. Conclude with `Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) h`. Establish `hmin : (p ^ k).minFac = p`.

Establish `h2 : (p ^ k).minFac.Prime` using `Nat.minFac_prime (Nat.one_lt_pow hk0 hp.out.one_lt).ne'`. Conclude with `(Nat.prime_dvd_prime_iff_eq h2 hp.out).1 (h2.dvd_of_dvd_pow (Nat.minFac_dvd _))`. Establish `hHn : H.Normal` using `Subgroup.normal_of_index_eq_minFac_card (by rw [hHi, hk, hmin])`. Use `set M := fixedOpen hLK H with hM`. Establish `hLM : L ≤ M` using `le_fixedOpen hLK H`.

Establish `hMK : M ≤ K` using `fixedOpen_le hLK H`. Establish `hcycM : IsCyclic ((K : Subgroup G) ⧸ (M : Subgroup G).subgroupOf K)` using `isCyclic_of_prime_card (p := p) (by`. Rewrite using `[card_quotient_eq_relIndex, hM, relIndex_fixedOpen_eq_index, hHi])`. Establish `hPM : IsPGroup p ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M)` using `(hP.to_subgroup H).of_equiv (galFixedEquiv hLK H).symm`. Establish `hLMn : (L : Subgroup G).relIndex M = p ^ (k - 1)`.

Rewrite using `[hM, relIndex_fixedOpen, hH]`. Establish `hlt : p ^ (k - 1) < n`. Rewrite using `[← hn, ← card_quotient_eq_relIndex, hk]`. Conclude with `Nat.pow_lt_pow_right hp.out.one_lt (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos)`. Take `⟨hs, hker⟩` from `ih _ hlt hLM hLMn hPM`.

Conclude with `⟨D.reciprocity_surjective_of_tower hax hLM hMK hs (reciprocity_bijective_of_isCyclic (D := D) hMK hax hcycM).2, D.ker_reciprocity_le_of_tower hax hLM hMK hcycM hs hker⟩`.
-/
theorem reciprocity_of_isPGroup {p : ℕ} [hp : Fact p.Prime] (n : ℕ) :
    ∀ {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal],
      (L : Subgroup G).relIndex K = n →
      IsPGroup p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) →
      Function.Surjective (D.reciprocity hLK hax) ∧
        (D.reciprocity hLK hax).ker ≤ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L hLK _ hn hP
  by_cases hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)
  · have hb := reciprocity_bijective_of_isCyclic (D := D) hLK hax hcyc
    refine ⟨hb.2, fun q hq => ?_⟩
    rw [(injective_iff_map_eq_one _).1 hb.1 q hq]
    exact Subgroup.one_mem _
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hcyc (@isCyclic_of_subsingleton _ _ (Nat.card_eq_one_iff_unique.1 hk).1)

  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p
    (pow_dvd_pow p (Nat.sub_le k 1) |>.trans hk.symm.dvd)
  have hpk : p ^ (k - 1) * p = p ^ k := by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
  have hHi : H.index = p := by
    have h := H.card_mul_index
    rw [hH, hk, ← hpk] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) h
  have hmin : (p ^ k).minFac = p := by
    have h2 : (p ^ k).minFac.Prime := Nat.minFac_prime (Nat.one_lt_pow hk0 hp.out.one_lt).ne'
    exact (Nat.prime_dvd_prime_iff_eq h2 hp.out).1 (h2.dvd_of_dvd_pow (Nat.minFac_dvd _))
  have hHn : H.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hHi, hk, hmin])
  set M := fixedOpen hLK H with hM
  have hLM : L ≤ M := le_fixedOpen hLK H
  have hMK : M ≤ K := fixedOpen_le hLK H

  have hcycM : IsCyclic ((K : Subgroup G) ⧸ (M : Subgroup G).subgroupOf K) :=
    isCyclic_of_prime_card (p := p) (by
      rw [card_quotient_eq_relIndex, hM, relIndex_fixedOpen_eq_index, hHi])

  have hPM : IsPGroup p ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) :=
    (hP.to_subgroup H).of_equiv (galFixedEquiv hLK H).symm
  have hLMn : (L : Subgroup G).relIndex M = p ^ (k - 1) := by
    rw [hM, relIndex_fixedOpen, hH]
  have hlt : p ^ (k - 1) < n := by
    rw [← hn, ← card_quotient_eq_relIndex, hk]
    exact Nat.pow_lt_pow_right hp.out.one_lt (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos)
  obtain ⟨hs, hker⟩ := ih _ hlt hLM hLMn hPM
  exact ⟨D.reciprocity_surjective_of_tower hax hLM hMK hs
      (reciprocity_bijective_of_isCyclic (D := D) hMK hax hcycM).2,
    D.ker_reciprocity_le_of_tower hax hLM hMK hcycM hs hker⟩

end PGroup

end ClassFieldData

end GroundTheory.LocalField.Abstract
