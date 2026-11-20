import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ResNormal
import Mathlib

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Simplify using `only [PL, Subgroup.mem_iInf]`.
-/
private theorem mem_PL {l : ℕ} {Γ : Type} [Group Γ] [TopologicalSpace Γ] {H : Subgroup Γ} {x : Γ} :
    x ∈ PL l H ↔ ∀ U : OpenNormalSubgroup Γ, (∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U) → x ∈ U.toSubgroup := by
  simp only [PL, Subgroup.mem_iInf]

/- English proof (translation)
Use `⟨fun h g => ?_, fun h x => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `h (g : G ⧸ N)`. Conclude with `⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective x`. Take `⟨k, hk⟩` from `h g`.

Conclude with `⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩`.
-/
private theorem pq_iff (l : ℕ) (G : Type) [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup l (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ l ^ k ∈ N := by
  refine ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

/- English proof (translation)
Use `haveI : Finite (Γ ⧸ K) := K.quotient_finite_of_isOpen hK`. Use `haveI : K.FiniteIndex := K.finiteIndex_of_finite_quotient`. Establish `hKc : IsClosed (K : Set Γ)` using `OpenSubgroup.isClosed ⟨K, hK⟩`. Establish `hCo : IsOpen (K.normalCore : Set Γ)` using `Subgroup.isOpen_of_isClosed_of_finiteIndex _ (K.normalCore_isClosed hKc)`. Set `C : OpenNormalSubgroup Γ` to `{ toOpenSubgroup := ⟨K.normalCore, hCo⟩ isNormal' := K.normalCore_normal }`.

Conclude with `⟨C, Subgroup.normal_le_normalCore.mpr hP, K.normalCore_le⟩`.
-/
private theorem exists_core {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K P : Subgroup Γ) [P.Normal] (hK : IsOpen (K : Set Γ)) (hP : P ≤ K) :
    ∃ U : OpenNormalSubgroup Γ, P ≤ U.toSubgroup ∧ U.toSubgroup ≤ K := by
  haveI : Finite (Γ ⧸ K) := K.quotient_finite_of_isOpen hK
  haveI : K.FiniteIndex := K.finiteIndex_of_finite_quotient
  have hKc : IsClosed (K : Set Γ) := OpenSubgroup.isClosed ⟨K, hK⟩
  have hCo : IsOpen (K.normalCore : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (K.normalCore_isClosed hKc)
  let C : OpenNormalSubgroup Γ :=
    { toOpenSubgroup := ⟨K.normalCore, hCo⟩
      isNormal' := K.normalCore_normal }
  exact ⟨C, Subgroup.normal_le_normalCore.mpr hP, K.normalCore_le⟩

/- English proof (translation)
Introduce `l _ Γ _ _ _ _ _ H _ hHo`. Establish `hHc : IsClosed (H : Set Γ)` using `OpenSubgroup.isClosed ⟨H, hHo⟩`. Establish `cond_le : ∀ U : OpenNormalSubgroup Γ, (∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U) → PL l H ≤ U.toSubgroup` using `fun U hU x hx => mem_PL.mp hx U hU`. Establish `hnorm : (PL l H).Normal` using `⟨fun x hx g => mem_PL.mpr fun U hU => U.isNormal'.conj_mem _ (mem_PL.mp hx U hU) g⟩`. Establish `hclosed : IsClosed (PL l H : Set Γ)`.

Simplify using `only [PL, Subgroup.coe_iInf]`. Conclude with `isClosed_iInter fun U => isClosed_iInter fun _ => U.toOpenSubgroup.isClosed`. Set `HU : OpenNormalSubgroup Γ` to `{ toOpenSubgroup := ⟨H, hHo⟩, isNormal' := inferInstance }`. Establish `hle : PL l H ≤ H`. Establish `hc : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ HU`.

Introduce `h hh`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, pow_one]`. Conclude with `hh`. Conclude with `cond_le HU hc`.

Take `⟨hPn, hPc, -, hPcond⟩` from `proLResOf_normal l Γ H hHc`. Establish `heq : PL l H = proLResOf l H` using `by haveI := hPn`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Assume the negation of the conclusion as `hxP`.

Establish `hsI` using `ProfiniteGrp.closedSubgroup_eq_sInf_open (⟨proLResOf l H, hPc⟩ : ClosedSubgroup Γ)`. Establish `h2 : x ∉ ((⟨proLResOf l H, hPc⟩ : ClosedSubgroup Γ) : Subgroup Γ)` using `hxP`. Rewrite `h2` using `[hsI, Subgroup.mem_sInf]`. Use `push_neg at h2`. Take `⟨K, ⟨hKo, hPK⟩, hxK⟩` from `h2`.

Take `⟨U, hPU, hUK⟩` from `exists_core K (proLResOf l H) hKo hPK`. Conclude with `hxK (hUK (mem_PL.mp hx U (hPcond U hPU)))`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Rewrite using `[mem_PL]`. Introduce `U hU`.

Set `N : OpenNormalSubgroup H` to `{ toOpenSubgroup := ⟨U.toSubgroup.comap H.subtype, U.toOpenSubgroup.isOpen.preimage continuous_subtype_val⟩ isNormal' := Subgroup.Normal.comap U.isNormal' _ }`. Use `haveI : N.toSubgroup.Normal := N.isNormal'`. Establish `hpg : IsPGroup l (H ⧸ N.toSubgroup)` using `(pq_iff l H _).mpr fun g => hU g g.2`. Conclude with `mem_proLRes.mp hy N hpg`. Establish `hiff : ∀ U : OpenNormalSubgroup Γ, PL l H ≤ U.toSubgroup ↔ ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U`.

Introduce `U`. Use `⟨fun h => ?_, cond_le U⟩` and prove the remaining obligations. Conclude with `hPcond U (heq ▸ h)`. Establish `hbot : PL l H = ⊥ ↔ IsProL l H`. Rewrite using `[isProL_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hb N g`. Set `K : Subgroup Γ` to `N.toSubgroup.map H.subtype`. Establish `hKo : IsOpen (K : Set Γ)`. Rewrite using `[Subgroup.coe_map]`.

Conclude with `hHo.isOpenMap_subtype_val _ N.toOpenSubgroup.isOpen`. Take `⟨U, -, hUK⟩` from `exists_core K ⊥ hKo bot_le`. Take `⟨e, he⟩` from `(hiff U).mp (by rw [hb]; exact bot_le) g g.2`. Use `⟨e, ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hyg⟩` from `Subgroup.mem_map.mp (hUK he)`.

Establish `hy' : y = g ^ l ^ e` using `Subtype.ext hyg`. Rewrite using `[← hy']`. Conclude with `hy`. Introduce `hP`. Rewrite using `[eq_bot_iff]`.

Introduce `x hx`. Rewrite using `[Subgroup.mem_bot]`. Establish `key : ∀ W : OpenNormalSubgroup Γ, x ∈ W.toSubgroup`. Introduce `W`. Apply `cond_le W _ hx` to reduce the goal to its premises.

Introduce `h hh`. Set `N : OpenNormalSubgroup H` to `{ toOpenSubgroup := ⟨W.toSubgroup.comap H.subtype, W.toOpenSubgroup.isOpen.preimage continuous_subtype_val⟩ isNormal' := Subgroup.Normal.comap W.isNormal' _ }`. Take `⟨k, hk⟩` from `hP N ⟨h, hh⟩`. Conclude with `⟨k, hk⟩`. Assume the negation of the conclusion as `hne`.

Take `⟨U, hU⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_compl_singleton (x := x)) (by simpa [eq_comm] using hne)`. Conclude with `hU (key U) rfl`. Conclude with `⟨hnorm, hclosed, hle, hiff, hbot, heq⟩`.
-/
theorem UpperTheory.V.Pa.pl_props :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (H : Subgroup Γ) [H.Normal], IsOpen (H : Set Γ) → (PL l H).Normal ∧ IsClosed (PL l H : Set Γ) ∧ PL l H ≤ H ∧ (∀ U : OpenNormalSubgroup Γ, PL l H ≤ U.toSubgroup ↔ ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U) ∧ (PL l H = ⊥ ↔ IsProL l H) ∧ PL l H = proLResOf l H := by
  intro l _ Γ _ _ _ _ _ H _ hHo
  have hHc : IsClosed (H : Set Γ) := OpenSubgroup.isClosed ⟨H, hHo⟩
  have cond_le : ∀ U : OpenNormalSubgroup Γ, (∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U) →
      PL l H ≤ U.toSubgroup :=
    fun U hU x hx => mem_PL.mp hx U hU
  have hnorm : (PL l H).Normal :=
    ⟨fun x hx g => mem_PL.mpr fun U hU => U.isNormal'.conj_mem _ (mem_PL.mp hx U hU) g⟩
  have hclosed : IsClosed (PL l H : Set Γ) := by
    simp only [PL, Subgroup.coe_iInf]
    exact isClosed_iInter fun U => isClosed_iInter fun _ => U.toOpenSubgroup.isClosed
  let HU : OpenNormalSubgroup Γ := { toOpenSubgroup := ⟨H, hHo⟩, isNormal' := inferInstance }
  have hle : PL l H ≤ H := by
    have hc : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ HU := by
      intro h hh
      refine ⟨0, ?_⟩
      rw [pow_zero, pow_one]
      exact hh
    exact cond_le HU hc
  obtain ⟨hPn, hPc, -, hPcond⟩ := proLResOf_normal l Γ H hHc
  have heq : PL l H = proLResOf l H := by
    haveI := hPn
    apply le_antisymm
    · intro x hx
      by_contra hxP
      have hsI := ProfiniteGrp.closedSubgroup_eq_sInf_open
        (⟨proLResOf l H, hPc⟩ : ClosedSubgroup Γ)
      have h2 : x ∉ ((⟨proLResOf l H, hPc⟩ : ClosedSubgroup Γ) : Subgroup Γ) := hxP
      rw [hsI, Subgroup.mem_sInf] at h2
      push_neg at h2
      obtain ⟨K, ⟨hKo, hPK⟩, hxK⟩ := h2
      obtain ⟨U, hPU, hUK⟩ := exists_core K (proLResOf l H) hKo hPK
      exact hxK (hUK (mem_PL.mp hx U (hPcond U hPU)))
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_PL]
      intro U hU
      let N : OpenNormalSubgroup H :=
        { toOpenSubgroup := ⟨U.toSubgroup.comap H.subtype,
            U.toOpenSubgroup.isOpen.preimage continuous_subtype_val⟩
          isNormal' := Subgroup.Normal.comap U.isNormal' _ }
      haveI : N.toSubgroup.Normal := N.isNormal'
      have hpg : IsPGroup l (H ⧸ N.toSubgroup) :=
        (pq_iff l H _).mpr fun g => hU g g.2
      exact mem_proLRes.mp hy N hpg
  have hiff : ∀ U : OpenNormalSubgroup Γ,
      PL l H ≤ U.toSubgroup ↔ ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U := by
    intro U
    refine ⟨fun h => ?_, cond_le U⟩
    exact hPcond U (heq ▸ h)
  have hbot : PL l H = ⊥ ↔ IsProL l H := by
    rw [isProL_iff]
    constructor
    · intro hb N g
      let K : Subgroup Γ := N.toSubgroup.map H.subtype
      have hKo : IsOpen (K : Set Γ) := by
        rw [Subgroup.coe_map]
        exact hHo.isOpenMap_subtype_val _ N.toOpenSubgroup.isOpen
      obtain ⟨U, -, hUK⟩ := exists_core K ⊥ hKo bot_le
      obtain ⟨e, he⟩ := (hiff U).mp (by rw [hb]; exact bot_le) g g.2
      refine ⟨e, ?_⟩
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp (hUK he)
      have hy' : y = g ^ l ^ e := Subtype.ext hyg
      rw [← hy']
      exact hy
    · intro hP
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have key : ∀ W : OpenNormalSubgroup Γ, x ∈ W.toSubgroup := by
        intro W
        apply cond_le W _ hx
        intro h hh
        let N : OpenNormalSubgroup H :=
          { toOpenSubgroup := ⟨W.toSubgroup.comap H.subtype,
              W.toOpenSubgroup.isOpen.preimage continuous_subtype_val⟩
            isNormal' := Subgroup.Normal.comap W.isNormal' _ }
        obtain ⟨k, hk⟩ := hP N ⟨h, hh⟩
        exact ⟨k, hk⟩
      by_contra hne
      obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (isOpen_compl_singleton (x := x)) (by simpa [eq_comm] using hne)
      exact hU (key U) rfl
  exact ⟨hnorm, hclosed, hle, hiff, hbot, heq⟩
