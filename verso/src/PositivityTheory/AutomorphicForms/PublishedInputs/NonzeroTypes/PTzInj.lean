import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_TzInj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce and unpack `g ⟨hg, hP⟩`. Use `⟨hg, fun i j => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, e⟩` from `hP i j`. Conclude with `⟨y, Ideal.pow_le_pow_right h hy, e⟩`.
-/
theorem KC_anti {n r r' : ℕ} (h : r ≤ r') : KC k n r' ⊆ KC k n r := by
  rintro g ⟨hg, hP⟩
  refine ⟨hg, fun i j => ?_⟩
  obtain ⟨y, hy, e⟩ := hP i j
  exact ⟨y, Ideal.pow_le_pow_right h hy, e⟩

/- English proof (translation)
Take `⟨y, -, rfl⟩` from `hx 0`. Establish `hy : ∀ r : ℕ, y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r`. Introduce `r`. Take `⟨z, hz, e⟩` from `hx r`. Establish `: z = y` using `Subtype.val_injective e`.

Conclude with `this ▸ hz`. Establish `hmem : y ∈ ⨅ r : ℕ, IsLocalRing.maximalIdeal 𝒪[k] ^ r` using `(Submodule.mem_iInf _).2 hy`. Rewrite `hmem` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top]`. Rewrite using `[(Ideal.mem_bot).1 hmem, map_zero]`.
-/
theorem eq_zero_of_inPow {x : k} (hx : ∀ r, InPow r x) : x = 0 := by
  obtain ⟨y, -, rfl⟩ := hx 0
  have hy : ∀ r : ℕ, y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
    intro r
    obtain ⟨z, hz, e⟩ := hx r
    have : z = y := Subtype.val_injective e
    exact this ▸ hz
  have hmem : y ∈ ⨅ r : ℕ, IsLocalRing.maximalIdeal 𝒪[k] ^ r := (Submodule.mem_iInf _).2 hy
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top] at hmem
  rw [(Ideal.mem_bot).1 hmem, map_zero]

/- English proof (translation)
Use extensionality with `i j`. Establish `h` using `eq_zero_of_inPow (fun r => (hg r).2 i j)`. Rewrite `h` using `[sub_eq_zero]`. Rewrite using `[h]`. Simplify using `[Matrix.one_apply]`.
-/
theorem eq_one_of_KC {n : ℕ} {g : GL (Fin n) k} (hg : ∀ r, g ∈ KC k n r) : g = 1 := by
  ext i j
  have h := eq_zero_of_inPow (fun r => (hg r).2 i j)
  rw [sub_eq_zero] at h
  rw [h]
  simp [Matrix.one_apply]

/- English proof (translation)
Establish `hcl : ∀ r, IsClosed (KC k n r)`. Introduce `r`. Use `Subgroup.isClosed_of_isOpen (KCg k n r) (by rw [hsub r]; exact hop r)` as an intermediate fact. Rewrite `this` using `[hsub r]`. Then use the resulting hypothesis. Establish `hst : (KO k (Fin n) : Set (GL (Fin n) k)) ∩ ⋂ r, (KC k n r ∩ Uᶜ) = ∅`.

Use `Set.eq_empty_iff_forall_notMem.2 fun g hg => ?_` and prove the remaining obligations. Establish `hg'` using `Set.mem_iInter.1 hg.2`. Establish `h1' : g = 1` using `eq_one_of_KC fun r => (hg' r).1`. Conclude with `(hg' 0).2 (h1' ▸ h1)`. Establish `hdt : Directed (· ⊇ ·) (fun r => KC k n r ∩ Uᶜ)`.

Introduce `a b`. Conclude with `⟨max a b, Set.inter_subset_inter_left _ (KC_anti (le_max_left a b)), Set.inter_subset_inter_left _ (KC_anti (le_max_right a b))⟩`. Take `⟨r, hr⟩` from `(GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).elim_directed_family_closed (fun r => KC k n r ∩ Uᶜ) (fun r => (hcl r).inter hU.isClosed_compl) hst hdt`. Use `⟨r, fun g hg => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hgU`.

Establish `: g ∈ (KO k (Fin n) : Set (GL (Fin n) k)) ∩ (KC k n r ∩ Uᶜ)` using `⟨hg.1, hg, hgU⟩`. Rewrite `this` using `[hr]`. Conclude with `this`.
-/
theorem exists_KC_subset {n : ℕ} (hsub : ∀ r, ((KCg k n r : Set (GL (Fin n) k)) = KC k n r))
    (hop : ∀ r, IsOpen (KC k n r)) (U : Set (GL (Fin n) k)) (hU : IsOpen U) (h1 : (1 : GL (Fin n) k) ∈ U) :
    ∃ r, KC k n r ⊆ U := by
  have hcl : ∀ r, IsClosed (KC k n r) := by
    intro r
    have := Subgroup.isClosed_of_isOpen (KCg k n r) (by rw [hsub r]; exact hop r)
    rwa [hsub r] at this
  have hst : (KO k (Fin n) : Set (GL (Fin n) k)) ∩ ⋂ r, (KC k n r ∩ Uᶜ) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun g hg => ?_
    have hg' := Set.mem_iInter.1 hg.2
    have h1' : g = 1 := eq_one_of_KC fun r => (hg' r).1
    exact (hg' 0).2 (h1' ▸ h1)
  have hdt : Directed (· ⊇ ·) (fun r => KC k n r ∩ Uᶜ) := by
    intro a b
    exact ⟨max a b, Set.inter_subset_inter_left _ (KC_anti (le_max_left a b)),
      Set.inter_subset_inter_left _ (KC_anti (le_max_right a b))⟩
  obtain ⟨r, hr⟩ := (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).elim_directed_family_closed
    (fun r => KC k n r ∩ Uᶜ) (fun r => (hcl r).inter hU.isClosed_compl) hst hdt
  refine ⟨r, fun g hg => ?_⟩
  by_contra hgU
  have : g ∈ (KO k (Fin n) : Set (GL (Fin n) k)) ∩ (KC k n r ∩ Uᶜ) := ⟨hg.1, hg, hgU⟩
  rw [hr] at this
  exact this

variable {n : ℕ} (G : Grp k n)

/- English proof (translation)
Establish `hz : G.zEl ϖ ∈ Subgroup.normalizer (unipRad k G.e : Set (GL (Fin n) k))` using `leviEmb_mem_normalizer k G.e _`. Use `(Subgroup.mem_normalizer_iff.1 (inv_mem hz) u).1 hu` as an intermediate fact. Simplify using `using this`.
-/
theorem conj_unip (ϖ : kˣ) {u : GL (Fin n) k} (hu : u ∈ unipRad k G.e) :
    (G.zEl ϖ)⁻¹ * u * G.zEl ϖ ∈ unipRad k G.e := by
  have hz : G.zEl ϖ ∈ Subgroup.normalizer (unipRad k G.e : Set (GL (Fin n) k)) :=
    leviEmb_mem_normalizer k G.e _
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem hz) u).1 hu
  simpa using this

/- English proof (translation)
Simplify using `[Grp.zN, Subgroup.mem_subgroupOf, Subgroup.mem_map, MulAut.conj_apply]`.
-/
theorem mem_zN (ϖ : kˣ) (u : ↥G.NO) :
    u ∈ G.zN ϖ 1 ↔ ∃ w ∈ G.NO, G.zEl ϖ * w * (G.zEl ϖ)⁻¹ = (u : GL (Fin n) k) := by
  simp [Grp.zN, Subgroup.mem_subgroupOf, Subgroup.mem_map, MulAut.conj_apply]

/- English proof (translation)
Simplify using `[Grp.PJ]`.
-/
theorem PJ_zero {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ) :
    G.PJ π r 0 = 0 := by
  simp [Grp.PJ]

end UpperTheory.TNZ.Grp.P_TzInj

namespace UpperTheory.TNZ.Grp

open P_TzInj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hlU hiw hPJ hkill hni hTE hKC ϖ hϖ V _ _ π hs x hx hT`. Establish `h3 : ∀ a b c : GL (Fin n) k, ∀ v : V, π (a * b * c) v = π a (π b (π c v))` using `fun a b c v => by`. Rewrite using `[map_mul, map_mul]`. Both sides reduce to the same expression. Establish `hQfin : Finite (↥G.NO ⧸ G.zN ϖ 1)` using `(hTE hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw ϖ hϖ 1).1`.

Set `_ : Fintype (↥G.NO ⧸ G.zN ϖ 1)` to `Fintype.ofFinite _`. Establish `hsum : ∑ c : ↥G.NO ⧸ G.zN ϖ 1, π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x = 0`. Establish `e0 : π (G.zEl ϖ)⁻¹ (G.Tz π ϖ 1 x) = 0` using `by rw [hT, map_zero]`. Establish `e1 : G.Tz π ϖ 1 x = ∑ c : ↥G.NO ⧸ G.zN ϖ 1, π ((Quotient.out c : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ 1) x)`. Unfold `Grp.Tz`.

Conclude with `finsum_eq_sum_of_fintype _`. Rewrite `e0` using `[e1, map_sum]`. Rewrite using `[← e0]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[h3, pow_one]`.

Set `U : Set (GL (Fin n) k)` to `{g | π g x = x} ∩ ⋂ c : ↥G.NO ⧸ G.zN ϖ 1, {g | π g (π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x) = π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x}`. Establish `hUo : IsOpen U` using `(hs x).inter (isOpen_iInter_of_finite fun c => hs _)`. Establish `hU1 : (1 : GL (Fin n) k) ∈ U`. Use `⟨by simp, Set.mem_iInter.2 fun c => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Take `⟨r0, hr0⟩` from `exists_KC_subset (fun r => (hKC hccB r).1) (fun r => (hKC hccB r).2.2.1) U hUo hU1`. Use `set r := max r0 G.lev with hr`. Establish `hrl : G.lev ≤ r` using `le_max_right _ _`. Establish `hKCr : KC k n r ⊆ U` using `(KC_anti (le_max_left _ _)).trans hr0`. Establish `hPJ'` using `hPJ hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC V π r hrl`.

Establish `hJfin : Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)` using `hPJ'.1`. Set `_ : Fintype (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)` to `Fintype.ofFinite _`. Establish `hlin : ∀ f : ↥G.NO ⧸ G.zN ϖ 1 → V, G.PJ π r (∑ c, f c) = ∑ c, G.PJ π r (f c)`. Introduce `f`. Simplify using `only [Grp.PJ, finsum_eq_sum_of_fintype, map_sum, Finset.smul_sum]`.

Conclude with `Finset.sum_comm`. Establish `hsum'` using `congrArg (G.PJ π r) hsum`. Rewrite `hsum'` using `[hlin, PJ_zero]`. Set `c1 : ↥G.NO ⧸ G.zN ϖ 1` to `QuotientGroup.mk (1 : ↥G.NO)`. Rewrite `hsum'` using `[Finset.sum_eq_single c1]`.

Establish `hu1 : (Quotient.out c1 : ↥G.NO) ∈ G.zN ϖ 1`. Establish `h : (QuotientGroup.mk (Quotient.out c1) : ↥G.NO ⧸ G.zN ϖ 1) = QuotientGroup.mk (1 : ↥G.NO)` using `Quotient.out_eq c1`. Use `QuotientGroup.eq.1 h` as an intermediate fact. Simplify using `using this`. Take `⟨w, hw, hwe⟩` from `(mem_zN G ϖ _).1 hu1`.

Establish `hyw : (G.zEl ϖ)⁻¹ * ((Quotient.out c1 : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ = w`. Rewrite using `[← hwe]`. Use `group`. Establish `hfix1 : π ((G.zEl ϖ)⁻¹ * ((Quotient.out c1 : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x = x`. Rewrite using `[hyw, hx w (hlU.1 w hw).1, (hlU.1 w hw).2, one_smul]`.

Rewrite `hsum'` using `[hfix1]`. Establish `hxfix : ∀ u ∈ KC k n r, π u x = x` using `fun u hu => (hKCr hu).1`. Rewrite `hsum'` using `[(hPJ'.2 x hxfix).2.2 hx]`. Establish `hcard : (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Conclude with `(smul_eq_zero.1 hsum').resolve_left hcard`.

Introduce `c _ hc`. Establish `hfix : ∀ u ∈ KC k n r, π u (π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x) = π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x` using `fun u hu => Set.mem_iInter.1 (hKCr hu).2 c`. Establish `hmem : ((Quotient.out c : ↥G.NO) : GL (Fin n) k) ∈ unipRad k G.e ⊓ KO k (Fin n)` using `(Quotient.out c).2`. Establish `hyU` using `conj_unip G ϖ (Subgroup.mem_inf.1 hmem).1`. Establish `hyK : (G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ ∉ KO k (Fin n)`.

Introduce `hK`. Apply `hc` to reduce the goal to its premises. Establish `hin : (Quotient.out c : ↥G.NO) ∈ G.zN ϖ 1`. Use `(mem_zN G ϖ _).2 ⟨_, Subgroup.mem_inf.2 ⟨hyU, hK⟩, ?_⟩` and prove the remaining obligations. Use `group`.

Establish `h : (QuotientGroup.mk (Quotient.out c) : ↥G.NO ⧸ G.zN ϖ 1) = QuotientGroup.mk (1 : ↥G.NO)` using `QuotientGroup.eq.2 (by simpa using inv_mem hin)`. Conclude with `(Quotient.out_eq c).symm.trans h`. Conclude with `hkill hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC hPJ V π r hrl x hx _ hfix (hni hcb hccB _ hyU hyK)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ c1) h`.
-/
theorem step_TzInj {n : ℕ} (G : Grp k n) : TorusCentreInjectiveProp G := by
  intro hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hlU hiw hPJ hkill hni hTE hKC ϖ hϖ V _ _ π hs x hx hT
  have h3 : ∀ a b c : GL (Fin n) k, ∀ v : V, π (a * b * c) v = π a (π b (π c v)) := fun a b c v => by
    rw [map_mul, map_mul]; rfl
  have hQfin : Finite (↥G.NO ⧸ G.zN ϖ 1) := (hTE hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw ϖ hϖ 1).1
  let _ : Fintype (↥G.NO ⧸ G.zN ϖ 1) := Fintype.ofFinite _

  have hsum : ∑ c : ↥G.NO ⧸ G.zN ϖ 1,
      π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x = 0 := by
    have e0 : π (G.zEl ϖ)⁻¹ (G.Tz π ϖ 1 x) = 0 := by rw [hT, map_zero]
    have e1 : G.Tz π ϖ 1 x = ∑ c : ↥G.NO ⧸ G.zN ϖ 1,
        π ((Quotient.out c : ↥G.NO) : GL (Fin n) k) (π (G.zEl ϖ ^ 1) x) := by
      unfold Grp.Tz
      exact finsum_eq_sum_of_fintype _
    rw [e1, map_sum] at e0
    rw [← e0]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [h3, pow_one]

  let U : Set (GL (Fin n) k) := {g | π g x = x} ∩ ⋂ c : ↥G.NO ⧸ G.zN ϖ 1,
    {g | π g (π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x) =
      π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x}
  have hUo : IsOpen U := (hs x).inter (isOpen_iInter_of_finite fun c => hs _)
  have hU1 : (1 : GL (Fin n) k) ∈ U := by
    refine ⟨by simp, Set.mem_iInter.2 fun c => ?_⟩
    simp
  obtain ⟨r0, hr0⟩ := exists_KC_subset (fun r => (hKC hccB r).1) (fun r => (hKC hccB r).2.2.1) U hUo hU1
  set r := max r0 G.lev with hr
  have hrl : G.lev ≤ r := le_max_right _ _
  have hKCr : KC k n r ⊆ U := (KC_anti (le_max_left _ _)).trans hr0
  have hPJ' := hPJ hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC V π r hrl
  have hJfin : Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := hPJ'.1
  let _ : Fintype (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := Fintype.ofFinite _
  have hlin : ∀ f : ↥G.NO ⧸ G.zN ϖ 1 → V,
      G.PJ π r (∑ c, f c) = ∑ c, G.PJ π r (f c) := by
    intro f
    simp only [Grp.PJ, finsum_eq_sum_of_fintype, map_sum, Finset.smul_sum]
    exact Finset.sum_comm
  have hsum' := congrArg (G.PJ π r) hsum
  rw [hlin, PJ_zero] at hsum'
  let c1 : ↥G.NO ⧸ G.zN ϖ 1 := QuotientGroup.mk (1 : ↥G.NO)
  rw [Finset.sum_eq_single c1] at hsum'
  ·
    have hu1 : (Quotient.out c1 : ↥G.NO) ∈ G.zN ϖ 1 := by
      have h : (QuotientGroup.mk (Quotient.out c1) : ↥G.NO ⧸ G.zN ϖ 1) = QuotientGroup.mk (1 : ↥G.NO) :=
        Quotient.out_eq c1
      have := QuotientGroup.eq.1 h
      simpa using this
    obtain ⟨w, hw, hwe⟩ := (mem_zN G ϖ _).1 hu1
    have hyw : (G.zEl ϖ)⁻¹ * ((Quotient.out c1 : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ = w := by
      rw [← hwe]; group
    have hfix1 : π ((G.zEl ϖ)⁻¹ * ((Quotient.out c1 : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x = x := by
      rw [hyw, hx w (hlU.1 w hw).1, (hlU.1 w hw).2, one_smul]
    rw [hfix1] at hsum'
    have hxfix : ∀ u ∈ KC k n r, π u x = x := fun u hu => (hKCr hu).1
    rw [(hPJ'.2 x hxfix).2.2 hx] at hsum'
    have hcard : (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact (smul_eq_zero.1 hsum').resolve_left hcard
  ·
    intro c _ hc
    have hfix : ∀ u ∈ KC k n r, π u (π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x) =
        π ((G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ) x :=
      fun u hu => Set.mem_iInter.1 (hKCr hu).2 c
    have hmem : ((Quotient.out c : ↥G.NO) : GL (Fin n) k) ∈ unipRad k G.e ⊓ KO k (Fin n) := (Quotient.out c).2
    have hyU := conj_unip G ϖ (Subgroup.mem_inf.1 hmem).1
    have hyK : (G.zEl ϖ)⁻¹ * ((Quotient.out c : ↥G.NO) : GL (Fin n) k) * G.zEl ϖ ∉ KO k (Fin n) := by
      intro hK
      apply hc
      have hin : (Quotient.out c : ↥G.NO) ∈ G.zN ϖ 1 := by
        refine (mem_zN G ϖ _).2 ⟨_, Subgroup.mem_inf.2 ⟨hyU, hK⟩, ?_⟩
        group
      have h : (QuotientGroup.mk (Quotient.out c) : ↥G.NO ⧸ G.zN ϖ 1) = QuotientGroup.mk (1 : ↥G.NO) :=
        QuotientGroup.eq.2 (by simpa using inv_mem hin)
      exact (Quotient.out_eq c).symm.trans h
    exact hkill hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC hPJ V π r hrl x hx _ hfix
      (hni hcb hccB _ hyU hyK)
  · intro h
    exact absurd (Finset.mem_univ c1) h

end UpperTheory.TNZ.Grp
