import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.EigInert

noncomputable section

open GlobalTheory.PRep GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.Eig

namespace HeckeFixedSubspaceSpan

section Gen

variable {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]

def fixSub (ρ : Representation ℂ H V) (P : Set V) : Subgroup H where
  carrier := {g | ∀ v ∈ P, ρ g v = v}
  one_mem' := by intro v _; simp
  mul_mem' := by
    intro a b ha hb v hv
    rw [map_mul, Module.End.mul_apply, hb v hv, ha v hv]
  inv_mem' := by
    intro a ha v hv
    have h := ha v hv
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [h]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_fixSub (ρ : Representation ℂ H V) (P : Set V) (g : H) :
    g ∈ fixSub ρ P ↔ ∀ v ∈ P, ρ g v = v := Iff.rfl

/- English proof (translation)
Establish `e : (fixSub ρ P : Set H) = ⋂ v ∈ P, {g : H | ρ g v = v}`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, mem_fixSub, Set.mem_iInter, Set.mem_setOf_eq]`. Rewrite using `[e]`. Conclude with `hP.isOpen_biInter (fun v _ => hρ v)`.
-/
theorem fixSub_open [TopologicalSpace H] (ρ : Representation ℂ H V)
    (hρ : ∀ v : V, IsOpen {g : H | ρ g v = v}) (P : Set V) (hP : P.Finite) :
    IsOpen (fixSub ρ P : Set H) := by
  have e : (fixSub ρ P : Set H) = ⋂ v ∈ P, {g : H | ρ g v = v} := by
    ext g
    simp only [SetLike.mem_coe, mem_fixSub, Set.mem_iInter, Set.mem_setOf_eq]
  rw [e]
  exact hP.isOpen_biInter (fun v _ => hρ v)

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Fintype.sum_equiv (MulAction.toPerm j) _ _ (fun r => ?_)` and prove the remaining obligations. Take `⟨s, hs⟩` from `QuotientGroup.mk_out_eq_mul S (j * r.out)`. Establish `e : (MulAction.toPerm j r : H ⧸ S) = (QuotientGroup.mk (j * r.out) : H ⧸ S)`. Rewrite using `[MulAction.toPerm_apply]`.

Conclude with `(congrArg (j • ·) (QuotientGroup.out_eq' r)).symm.trans (MulAction.Quotient.smul_mk S j r.out)`. Rewrite using `[e, hs, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hz s s.2]`.
-/
theorem avg_left (ρ : Representation ℂ H V) (S : Subgroup H) [Fintype (H ⧸ S)] (z : V)
    (hz : ∀ h ∈ S, ρ h z = z) (j : H) :
    ρ j (∑ r : H ⧸ S, ρ r.out z) = ∑ r : H ⧸ S, ρ r.out z := by
  rw [map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm j) _ _ (fun r => ?_)
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (j * r.out)
  have e : (MulAction.toPerm j r : H ⧸ S) = (QuotientGroup.mk (j * r.out) : H ⧸ S) := by
    rw [MulAction.toPerm_apply]
    exact (congrArg (j • ·) (QuotientGroup.out_eq' r)).symm.trans (MulAction.Quotient.smul_mk S j r.out)
  rw [e, hs, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hz s s.2]

/- English proof (translation)
Use `Fintype.sum_equiv (Equiv.mulRight (j : H ⧸ S)) _ _ (fun r => ?_)` and prove the remaining obligations. Take `⟨s, hs⟩` from `QuotientGroup.mk_out_eq_mul S (r.out * j)`. Establish `e : (r * (j : H ⧸ S)) = (QuotientGroup.mk (r.out * j) : H ⧸ S)`. Rewrite using `[QuotientGroup.mk_mul, QuotientGroup.out_eq']`. Use `show _ = ρ ((r * (j : H ⧸ S)).out) x`.

Rewrite using `[e, hs, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx s s.2]`.
-/
theorem avg_right (ρ : Representation ℂ H V) (S : Subgroup H) [S.Normal] [Fintype (H ⧸ S)] (x : V)
    (hx : ∀ h ∈ S, ρ h x = x) (j : H) :
    ∑ r : H ⧸ S, ρ r.out (ρ j x) = ∑ r : H ⧸ S, ρ r.out x := by
  refine Fintype.sum_equiv (Equiv.mulRight (j : H ⧸ S)) _ _ (fun r => ?_)
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (r.out * j)
  have e : (r * (j : H ⧸ S)) = (QuotientGroup.mk (r.out * j) : H ⧸ S) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  show _ = ρ ((r * (j : H ⧸ S)).out) x
  rw [e, hs, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx s s.2]

/- English proof (translation)
Simplify using `[hw]`.
-/
theorem avg_fixed (ρ : Representation ℂ H V) (S : Subgroup H) [Fintype (H ⧸ S)] (w : V)
    (hw : ∀ h, ρ h w = w) : ∑ r : H ⧸ S, ρ r.out w = Fintype.card (H ⧸ S) • w := by
  simp [hw]

/- English proof (translation)
Take `⟨n, f, g, hg⟩` from `(Submodule.mem_span_set').1 hwM`. Establish `hg' : ∀ i, ∃ (a : H) (b : V), (g i : V) = ρ a b - b` using `fun i => (g i).2`. Use `choose j v hjv using hg'`. Establish `hO` using `fixSub_open ρ hρ (Set.range v) (Set.finite_range v)`. Use `haveI : Finite (H ⧸ fixSub ρ (Set.range v)) := Subgroup.quotient_finite_of_isOpen _ hO`.

Use `haveI : (fixSub ρ (Set.range v)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Use `letI : Fintype (H ⧸ (fixSub ρ (Set.range v)).normalCore) := Fintype.ofFinite _`. Establish `hfix : ∀ i, ∀ h ∈ (fixSub ρ (Set.range v)).normalCore, ρ h (v i) = v i` using `fun i h hh => (mem_fixSub ρ _ h).1 (Subgroup.normalCore_le _ hh) (v i) ⟨i, rfl⟩`. Establish `h0 : ∑ r : H ⧸ (fixSub ρ (Set.range v)).normalCore, ρ r.out w = 0`. Rewrite using `[← hg]`.

Simplify using `only [map_sum, map_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.smul_sum, hjv i]`. Simplify using `only [map_sub, Finset.sum_sub_distrib]`.

Rewrite using `[avg_right ρ _ (v i) (hfix i) (j i), sub_self, smul_zero]`. Rewrite `h0` using `[avg_fixed ρ _ w hw, ← Nat.cast_smul_eq_nsmul ℂ]`. Break down `smul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `absurd (Nat.cast_eq_zero.mp h) Fintype.card_ne_zero`. Conclude with `h`.
-/
theorem sep_span [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (ρ : Representation ℂ H V) (hρ : ∀ v : V, IsOpen {g : H | ρ g v = v}) (w : V) (hw : ∀ h, ρ h w = w)
    (hwM : w ∈ Submodule.span ℂ {u | ∃ (j : H) (v : V), u = ρ j v - v}) : w = 0 := by
  obtain ⟨n, f, g, hg⟩ := (Submodule.mem_span_set').1 hwM
  have hg' : ∀ i, ∃ (a : H) (b : V), (g i : V) = ρ a b - b := fun i => (g i).2
  choose j v hjv using hg'
  have hO := fixSub_open ρ hρ (Set.range v) (Set.finite_range v)
  haveI : Finite (H ⧸ fixSub ρ (Set.range v)) := Subgroup.quotient_finite_of_isOpen _ hO
  haveI : (fixSub ρ (Set.range v)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  letI : Fintype (H ⧸ (fixSub ρ (Set.range v)).normalCore) := Fintype.ofFinite _
  have hfix : ∀ i, ∀ h ∈ (fixSub ρ (Set.range v)).normalCore, ρ h (v i) = v i := fun i h hh =>
    (mem_fixSub ρ _ h).1 (Subgroup.normalCore_le _ hh) (v i) ⟨i, rfl⟩
  have h0 : ∑ r : H ⧸ (fixSub ρ (Set.range v)).normalCore, ρ r.out w = 0 := by
    rw [← hg]
    simp only [map_sum, map_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [← Finset.smul_sum, hjv i]
    simp only [map_sub, Finset.sum_sub_distrib]
    rw [avg_right ρ _ (v i) (hfix i) (j i), sub_self, smul_zero]
  rw [avg_fixed ρ _ w hw, ← Nat.cast_smul_eq_nsmul ℂ] at h0
  rcases smul_eq_zero.mp h0 with h | h
  · exact absurd (Nat.cast_eq_zero.mp h) Fintype.card_ne_zero
  · exact h

/- English proof (translation)
Distinguish the cases in `hwM : w ∈ Submodule.span ℂ {u | ∃ (j : H) (v : V), u = ρ j v - v}`. Conclude with `sep_span ρ hρ w hw hwM`. Take `⟨φ, hφw, hφM⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hwM inferInstance`. It suffices to derive a contradiction. Apply `hφw` to reduce the goal to its premises.

Apply `hφ` to reduce the goal to its premises. Introduce `h`. Use extensionality with `v`. Establish `hm : ρ h v - v ∈ Submodule.span ℂ {u | ∃ (j : H) (v : V), u = ρ j v - v}` using `Submodule.subset_span ⟨h, v, rfl⟩`. Establish `h1 : φ (ρ h v - v) = 0`.

Establish `h2` using `Submodule.mem_map_of_mem (f := φ) hm`. Rewrite `h2` using `[hφM]`. Conclude with `(Submodule.mem_bot ℂ).mp h2`. Rewrite `h1` using `[map_sub, sub_eq_zero]`. Simplify using `using h1`.
-/
theorem sep [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (ρ : Representation ℂ H V) (hρ : ∀ v : V, IsOpen {g : H | ρ g v = v}) (w : V) (hw : ∀ h, ρ h w = w)
    (hφ : ∀ φ : Module.Dual ℂ V, (∀ h, φ ∘ₗ ρ h = φ) → φ w = 0) : w = 0 := by
  by_cases hwM : w ∈ Submodule.span ℂ {u | ∃ (j : H) (v : V), u = ρ j v - v}
  · exact sep_span ρ hρ w hw hwM
  · obtain ⟨φ, hφw, hφM⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hwM inferInstance
    exfalso
    apply hφw
    apply hφ
    intro h
    ext v
    have hm : ρ h v - v ∈ Submodule.span ℂ {u | ∃ (j : H) (v : V), u = ρ j v - v} :=
      Submodule.subset_span ⟨h, v, rfl⟩
    have h1 : φ (ρ h v - v) = 0 := by
      have h2 := Submodule.mem_map_of_mem (f := φ) hm
      rw [hφM] at h2
      exact (Submodule.mem_bot ℂ).mp h2
    rw [map_sub, sub_eq_zero] at h1
    simpa using h1

end Gen

section Main

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `h : ∀ h : J, ρ h (y : V) = ((1 : J →* ℂˣ) h : ℂ) • (y : V)` using `y.2`. Simplify using `using h ⟨k, hk⟩`.
-/
theorem fix_apply {ρ : Representation ℂ G V} {J : Subgroup G} (y : fixed ρ J) {k : G} (hk : k ∈ J) :
    ρ k (y : V) = y := by
  have h : ∀ h : J, ρ h (y : V) = ((1 : J →* ℂˣ) h : ℂ) • (y : V) := y.2
  simpa using h ⟨k, hk⟩

def Dsub (J : Subgroup G) (t : G) : Subgroup J := (J.map (MulAut.conj t).toMonoidHom).subgroupOf J

/- English proof (translation)
Rewrite using `[Dsub, Subgroup.mem_subgroupOf, Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, hxd⟩`. Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxd`. Rewrite using `[← hxd]`.

Simplify `hx` using `[mul_assoc]`. Introduce `h`. Use `⟨t⁻¹ * d * t, h, ?_⟩` and prove the remaining obligations. Simplify using `[mul_assoc]`.
-/
theorem mem_Dsub (J : Subgroup G) (t : G) (d : J) : d ∈ Dsub J t ↔ t⁻¹ * (d : G) * t ∈ J := by
  rw [Dsub, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxd⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxd
    rw [← hxd]
    simpa [mul_assoc] using hx
  · intro h
    refine ⟨t⁻¹ * d * t, h, ?_⟩
    simp [mul_assoc]

def iota (J : Subgroup G) (t : G) (r : J ⧸ Dsub J t) : G ⧸ J := (((r.out : G) * t : G) : G ⧸ J)

/- English proof (translation)
Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul J ((r.out : G) * t)`. Conclude with `⟨k, k.2, hk⟩`.
-/
theorem out_iota (J : Subgroup G) (t : G) (r : J ⧸ Dsub J t) :
    ∃ k ∈ J, (iota J t r).out = (r.out : G) * t * k := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul J ((r.out : G) * t)
  exact ⟨k, k.2, hk⟩

/- English proof (translation)
Introduce `r1 r2 h`. Unfold `iota at h`. Rewrite `h` using `[QuotientGroup.eq]`. Rewrite using `[← QuotientGroup.out_eq' r1, ← QuotientGroup.out_eq' r2, QuotientGroup.eq, mem_Dsub]`. Simplify `h` using `[mul_assoc]`.
-/
theorem iota_inj (J : Subgroup G) (t : G) : Function.Injective (iota J t) := by
  intro r1 r2 h
  unfold iota at h
  rw [QuotientGroup.eq] at h
  rw [← QuotientGroup.out_eq' r1, ← QuotientGroup.out_eq' r2, QuotientGroup.eq, mem_Dsub]
  simpa [mul_assoc] using h

/- English proof (translation)
Take `⟨x, hx, z, hz, hq⟩` from `h`. Use `⟨(QuotientGroup.mk ⟨x, hx⟩ : J ⧸ Dsub J t), ?_⟩` and prove the remaining obligations. Take `⟨d, hd⟩` from `QuotientGroup.mk_out_eq_mul (Dsub J t) (⟨x, hx⟩ : J)`. Establish `hd'` using `(mem_Dsub J t d).1 d.2`. Rewrite using `[← QuotientGroup.out_eq' q]`.

Unfold `iota`. Rewrite using `[hd, QuotientGroup.eq, hq]`. Establish `e : ((((⟨x, hx⟩ : J) * (d : J) : J) : G) * t)⁻¹ * (x * t * z) = (t⁻¹ * ((d : J) : G) * t)⁻¹ * z`. Simplify using `only [Subgroup.coe_mul]`. Use `group`.

Rewrite using `[e]`. Conclude with `J.mul_mem (J.inv_mem hd') hz`.
-/
theorem mem_range_iota (J : Subgroup G) (t : G) (q : G ⧸ J)
    (h : ∃ x ∈ J, ∃ z ∈ J, q.out = x * t * z) : ∃ r, iota J t r = q := by
  obtain ⟨x, hx, z, hz, hq⟩ := h
  refine ⟨(QuotientGroup.mk ⟨x, hx⟩ : J ⧸ Dsub J t), ?_⟩
  obtain ⟨d, hd⟩ := QuotientGroup.mk_out_eq_mul (Dsub J t) (⟨x, hx⟩ : J)
  have hd' := (mem_Dsub J t d).1 d.2
  rw [← QuotientGroup.out_eq' q]
  unfold iota
  rw [hd, QuotientGroup.eq, hq]
  have e : ((((⟨x, hx⟩ : J) * (d : J) : J) : G) * t)⁻¹ * (x * t * z) = (t⁻¹ * ((d : J) : G) * t)⁻¹ * z := by
    simp only [Subgroup.coe_mul]
    group
  rw [e]
  exact J.mul_mem (J.inv_mem hd') hz

/- English proof (translation)
Unfold `levOp`. Rewrite using `[finsum_eq_sum_of_support_subset (s := Finset.univ.image (iota J t)) _ ?hs]`. Rewrite using `[Finset.sum_image (fun a _ b _ hab => iota_inj J t hab), LinearMap.smul_apply, LinearMap.sum_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun r _ => ?_)` and prove the remaining obligations.

Take `⟨k, hk, hout⟩` from `out_iota J t r`. Establish `hmem : ∃ x ∈ J, ∃ z ∈ J, (iota J t r).out = x * t * z` using `⟨r.out, (r.out).2, k, hk, hout⟩`. Use `beta_reduce`. Rewrite using `[if_pos hmem, one_smul, LinearMap.comp_id, hout, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, fix_apply y hk]`. Introduce `q hq`.

Rewrite `hq` using `[Function.mem_support]`. Distinguish the cases in `h : ∃ x ∈ J, ∃ z ∈ J, q.out = x * t * z`. Take `⟨r, hr⟩` from `mem_range_iota J t q h`. Rewrite using `[Finset.coe_image]`. Conclude with `⟨r, by simp, hr⟩`.

Conclude with `absurd (by simp [h]) hq`.
-/
theorem levOp_eq (ρ : Representation ℂ G V) (K J : Subgroup G) (t : G) [Fintype (J ⧸ Dsub J t)]
    (y : fixed ρ J) :
    levOp ρ K J (fun g => if ∃ x ∈ J, ∃ z ∈ J, g = x * t * z then 1 else 0) LinearMap.id (y : V) =
      (((J.relIndex K : ℕ) : ℂ)⁻¹) • ∑ r : J ⧸ Dsub J t, ρ (r.out : G) (ρ t y) := by
  unfold levOp
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image (iota J t)) _ ?hs]
  · rw [Finset.sum_image (fun a _ b _ hab => iota_inj J t hab), LinearMap.smul_apply, LinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    obtain ⟨k, hk, hout⟩ := out_iota J t r
    have hmem : ∃ x ∈ J, ∃ z ∈ J, (iota J t r).out = x * t * z := ⟨r.out, (r.out).2, k, hk, hout⟩
    beta_reduce
    rw [if_pos hmem, one_smul, LinearMap.comp_id, hout, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, fix_apply y hk]
  · intro q hq
    rw [Function.mem_support] at hq
    by_cases h : ∃ x ∈ J, ∃ z ∈ J, q.out = x * t * z
    · obtain ⟨r, hr⟩ := mem_range_iota J t q h
      rw [Finset.coe_image]
      exact ⟨r, by simp, hr⟩
    · exact absurd (by simp [h]) hq

/- English proof (translation)
Set `ρJ : Representation ℂ J V` to `ρ.comp J.subtype`. Establish `hsm : ∀ v : V, IsOpen {g : J | ρJ g v = v}` using `fun v => (hρ v).preimage continuous_subtype_val`. Establish `hinv : ρ t⁻¹ (ρ t (y : V)) = y`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Establish `hz : ∀ h ∈ Dsub J t, ρJ h (ρ t y) = ρ t y`.

Introduce `h hh`. Establish `h1` using `(mem_Dsub J t h).1 hh`. Use `show ρ (h : G) (ρ t y) = ρ t y`. Establish `e : (h : G) = t * (t⁻¹ * h * t) * t⁻¹` using `by group`. Rewrite using `[e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hinv, fix_apply y h1]`.

Use `show ∑ r : J ⧸ Dsub J t, ρJ r.out (ρ t y) = _`. Establish `hw : ∀ g : J, ρJ g (∑ r : J ⧸ Dsub J t, ρJ r.out (ρ t y) - Fintype.card (J ⧸ Dsub J t) • (U y : V)) = ∑ r : J ⧸ Dsub J t, ρJ r.out (ρ t y) - Fintype.card (J ⧸ Dsub J t) • (U y : V)`. Introduce `g`. Rewrite using `[map_sub, map_nsmul, avg_left ρJ (Dsub J t) (ρ t y) hz g]`. Use `congr 2`.

Conclude with `fix_apply (U y) g.2`. Establish `hφ : ∀ φ : Module.Dual ℂ V, (∀ h, φ ∘ₗ ρJ h = φ) → φ (∑ r : J ⧸ Dsub J t, ρJ r.out (ρ t y) - Fintype.card (J ⧸ Dsub J t) • (U y : V)) = 0`. Introduce `φ hφ`. Rewrite using `[map_sub, map_nsmul, map_sum]`. Establish `e1 : ∀ r : J ⧸ Dsub J t, φ (ρJ r.out (ρ t y)) = φ (ρ t y)` using `fun r => by`.

Rewrite using `[← LinearMap.comp_apply, hφ]`. Simplify using `only [e1, Finset.sum_const, Finset.card_univ]`. Rewrite using `[hU y φ (fun x hx => hφ ⟨x, hx⟩), sub_self]`. Conclude with `sub_eq_zero.mp (sep ρJ hsm _ hw hφ)`.
-/
theorem key [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (J : Subgroup G) [CompactSpace J] (t : G) (U : Module.End ℂ (fixed ρ J))
    (hU : PositivityTheory.Lbc.IsHeckeOpG ρ J t U) (y : fixed ρ J) [Fintype (J ⧸ Dsub J t)] :
    ∑ r : J ⧸ Dsub J t, ρ (r.out : G) (ρ t y) = Fintype.card (J ⧸ Dsub J t) • (U y : V) := by
  let ρJ : Representation ℂ J V := ρ.comp J.subtype
  have hsm : ∀ v : V, IsOpen {g : J | ρJ g v = v} := fun v => (hρ v).preimage continuous_subtype_val
  have hinv : ρ t⁻¹ (ρ t (y : V)) = y := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hz : ∀ h ∈ Dsub J t, ρJ h (ρ t y) = ρ t y := by
    intro h hh
    have h1 := (mem_Dsub J t h).1 hh
    show ρ (h : G) (ρ t y) = ρ t y
    have e : (h : G) = t * (t⁻¹ * h * t) * t⁻¹ := by group
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hinv, fix_apply y h1]
  show ∑ r : J ⧸ Dsub J t, ρJ r.out (ρ t y) = _
  have hw : ∀ g : J, ρJ g (∑ r : J ⧸ Dsub J t, ρJ r.out (ρ t y) - Fintype.card (J ⧸ Dsub J t) • (U y : V)) =
      ∑ r : J ⧸ Dsub J t, ρJ r.out (ρ t y) - Fintype.card (J ⧸ Dsub J t) • (U y : V) := by
    intro g
    rw [map_sub, map_nsmul, avg_left ρJ (Dsub J t) (ρ t y) hz g]
    congr 2
    exact fix_apply (U y) g.2
  have hφ : ∀ φ : Module.Dual ℂ V, (∀ h, φ ∘ₗ ρJ h = φ) →
      φ (∑ r : J ⧸ Dsub J t, ρJ r.out (ρ t y) - Fintype.card (J ⧸ Dsub J t) • (U y : V)) = 0 := by
    intro φ hφ
    rw [map_sub, map_nsmul, map_sum]
    have e1 : ∀ r : J ⧸ Dsub J t, φ (ρJ r.out (ρ t y)) = φ (ρ t y) := fun r => by
      rw [← LinearMap.comp_apply, hφ]
    simp only [e1, Finset.sum_const, Finset.card_univ]
    rw [hU y φ (fun x hx => hφ ⟨x, hx⟩), sub_self]
  exact sub_eq_zero.mp (sep ρJ hsm _ hw hφ)

end Main

end HeckeFixedSubspaceSpan

open HeckeFixedSubspaceSpan in
/- English proof (translation)
Introduce `G _ _ _ V _ _ ρ hρ K J hJ hK hJK t U hU y`. Use `haveI : CompactSpace J := isCompact_iff_compactSpace.mp (hK.of_isClosed_subset (J.isClosed_of_isOpen hJ) (fun x hx => hJK hx))`. Establish `hDo : IsOpen ((Dsub J t : Subgroup J) : Set J)`. Establish `e : ((Dsub J t : Subgroup J) : Set J) = (fun d : J => t⁻¹ * (d : G) * t) ⁻¹' (J : Set G)`. Use extensionality with `d`.

Simplify using `only [SetLike.mem_coe, mem_Dsub, Set.mem_preimage]`. Rewrite using `[e]`. Conclude with `hJ.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)`. Use `haveI : Finite (J ⧸ Dsub J t) := Subgroup.quotient_finite_of_isOpen _ hDo`. Use `letI : Fintype (J ⧸ Dsub J t) := Fintype.ofFinite _`.

Rewrite using `[levOp_eq ρ K J t y, key ρ hρ J t U hU y, mul_smul, ← Nat.cast_smul_eq_nsmul ℂ, Fintype.card_eq_nat_card]`. Both sides reduce to the same expression.
-/
theorem heckeSum : HeckeSum := by
  intro G _ _ _ V _ _ ρ hρ K J hJ hK hJK t U hU y
  haveI : CompactSpace J :=
    isCompact_iff_compactSpace.mp (hK.of_isClosed_subset (J.isClosed_of_isOpen hJ) (fun x hx => hJK hx))
  have hDo : IsOpen ((Dsub J t : Subgroup J) : Set J) := by
    have e : ((Dsub J t : Subgroup J) : Set J) = (fun d : J => t⁻¹ * (d : G) * t) ⁻¹' (J : Set G) := by
      ext d
      simp only [SetLike.mem_coe, mem_Dsub, Set.mem_preimage]
    rw [e]
    exact hJ.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  haveI : Finite (J ⧸ Dsub J t) := Subgroup.quotient_finite_of_isOpen _ hDo
  letI : Fintype (J ⧸ Dsub J t) := Fintype.ofFinite _
  rw [levOp_eq ρ K J t y, key ρ hρ J t U hU y, mul_smul, ← Nat.cast_smul_eq_nsmul ℂ, Fintype.card_eq_nat_card]
  rfl

end PositivityTheory.Rg.BcB.F.Eig

end
