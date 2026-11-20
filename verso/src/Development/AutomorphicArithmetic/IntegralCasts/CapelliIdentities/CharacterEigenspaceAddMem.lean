import Mathlib

open scoped Classical

/- English proof (translation)
Introduce `k G V _ _ _ _ ρ H χ a b ha hb h`. Rewrite using `[map_add, ha h, hb h, smul_add]`.
-/
theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux1 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V},
      a ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        b ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
          ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (a + b) = (↑((χ : ↥H → kˣ) h) : k) • (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  rw [map_add, ha h, hb h, smul_add]

/- English proof (translation)
Introduce `k G V _ _ _ _ ρ H χ h`. Rewrite using `[map_zero, smul_zero]`.
-/
theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux2 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H),
      ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (0 : V) = (↑((χ : ↥H → kˣ) h) : k) • (0 : V) := by
  intro k G V _ _ _ _ ρ H χ h
  rw [map_zero, smul_zero]

/- English proof (translation)
Introduce `k G V _ _ _ _ ρ H χ c v hv h`. Rewrite using `[map_smul, hv h, smul_comm]`.
-/
theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux3 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V},
      v ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (c • v) = (↑((χ : ↥H → kˣ) h) : k) • c • v := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  rw [map_smul, hv h, smul_comm]

noncomputable def UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.eig :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
    fun {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
        (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦
      { carrier := {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v},
        add_mem' := @UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux1 k G V inst inst_1 inst_2 inst_3 ρ H χ, zero_mem' := UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux2 ρ H χ,
        smul_mem' := UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux3 ρ H χ : Submodule k V }

noncomputable def UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → Representation k G V → Subgroup G → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V)
        (H : Subgroup G) ↦
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.eig ρ H (1 : ↥H →* kˣ)

noncomputable def UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp :
    {G : Type} →
      [inst : Group G] →
        {V : Type} →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module ℂ V] →
              Representation ℂ G V → Subgroup G → Subgroup G → (G → ℂ) → (V →ₗ[ℂ] V) → V →ₗ[ℂ] V :=
    fun {G : Type} [Group G] {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ G V) (K K' : Subgroup G)
        (f : G → ℂ) (A : V →ₗ[ℂ] V) ↦
      (↑(K'.relIndex K) : ℂ)⁻¹ • ∑ᶠ (q : G ⧸ K'), f (Quotient.out q) • (ρ : G → V →ₗ[ℂ] V) (Quotient.out q) ∘ₗ A

noncomputable def UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.twTr :
    {G : Type} →
      [inst : Group G] →
        {V : Type} →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Subgroup G → Subgroup G → (G → ℂ) → (V →ₗ[ℂ] V) → ℂ :=
    fun {G : Type} [Group G] {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ G V) (K K' : Subgroup G)
        (f : G → ℂ) (A : V →ₗ[ℂ] V) ↦
      if h :
          ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ K', (UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K K' f A : V → V) v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ K' then
        (LinearMap.trace ℂ ↥(UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ K') :
            (↥(UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ K') →ₗ[ℂ] ↥(UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ K')) → ℂ)
          ((UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K K' f A).restrict h)
      else (0 : ℂ)

/- English proof (translation)
Introduce `H _ u a b ha hb x`. Rewrite using `[← mul_assoc, hb, ha]`.
-/
theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux11 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) {a b : H},
      a ∈ {k : H | ∀ (x : H), u (x * k) = u x} → b ∈ {k : H | ∀ (x : H), u (x * k) = u x} → ∀ (x : H), u (x * (a * b)) = u x := by
  intro H _ u a b ha hb x
  rw [← mul_assoc, hb, ha]

/- English proof (translation)
Introduce `H _ u a`. Rewrite using `[mul_one]`.
-/
theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux12 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) (a : H), u (a * (1 : H)) = u a := by
  intro H _ u a
  rw [mul_one]

/- English proof (translation)
Introduce `H _ u a ha x`. Use `ha (x * a⁻¹)` as an intermediate fact. Rewrite using `[← this, inv_mul_cancel_right]`.
-/
theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.algebra_smulCommClass_complex :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) {a : H},
      a ∈ {k : H | ∀ (x : H), u (x * k) = u x} → ∀ (x : H), u (x * a⁻¹) = u x := by
  intro H _ u a ha x
  have := ha (x * a⁻¹)
  rw [← this, inv_mul_cancel_right]

noncomputable def UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.rStab :
    {H : Type} → [inst : Group H] → (H → ℂ) → Subgroup H :=
    fun {H : Type} [inst : Group H] (u : H → ℂ) ↦
      { carrier := {k : H | ∀ (x : H), u (x * k) = u x}, mul_mem' := @UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux11 H inst u,
        one_mem' := UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux12 u, inv_mem' := @UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.algebra_smulCommClass_complex H inst u : Subgroup H }

noncomputable def UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trc :
    {G V : Type} →
      [inst : Group G] →
        [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Subgroup G → (G → ℂ) → ℂ :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
        (f : G → ℂ) ↦
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.twTr ρ K (K ⊓ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.rStab f ⊓ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.rStab fun (y : G) ↦ f y⁻¹) f LinearMap.id

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv a ha`. Simplify using `using hv ⟨a, ha⟩`. Introduce `hv a`. Simplify using `using hv a a.2`.
-/
private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.mem_fixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ H ↔ ∀ a ∈ H, ρ a v = v := by
  constructor
  · intro hv a ha
    simpa using hv ⟨a, ha⟩
  · intro hv a
    simpa using hv a a.2

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH`. Use `(hC.image (QuotientGroup.continuous_mk (N := H))).finite_of_discrete.subset ?_` and prove the remaining obligations. Introduce `q hq`. Conclude with `⟨_, hf _ hq, QuotientGroup.out_eq' q⟩`.
-/
private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.supp_finite {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G)) {C : Set G} (hC : IsCompact C)
    (f : G → ℂ) (hf : ∀ y, f y ≠ 0 → y ∈ C) :
    (Function.support fun q : G ⧸ H ↦ f (Quotient.out q)).Finite := by
  haveI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  refine (hC.image (QuotientGroup.continuous_mk (N := H))).finite_of_discrete.subset ?_
  intro q hq
  exact ⟨_, hf _ hq, QuotientGroup.out_eq' q⟩

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Establish `h : IsOpen ((I.subgroupOf K : Subgroup K) : Set K)` using `hI.preimage continuous_subtype_val`. Use `haveI := Subgroup.quotient_finite_of_isOpen _ h`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.relIndex_ne {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K I : Subgroup G) (hK : IsCompact (K : Set G))
    (hI : IsOpen (I : Set G)) : I.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have h : IsOpen ((I.subgroupOf K : Subgroup K) : Set K) := hI.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ h
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul H g`. Rewrite using `[hh, hF _ h.2]`.
-/
private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.out_mk {G M : Type} [Group G] (H : Subgroup G) (F : G → M)
    (hF : ∀ a ∈ H, ∀ y, F (y * a) = F y) (g : G) :
    F (Quotient.out (QuotientGroup.mk g : G ⧸ H)) = F g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hF _ h.2]

/- English proof (translation)
Use `haveI : Finite (J ⧸ I.subgroupOf J) := Nat.finite_of_card_ne_zero hne`. Use `haveI := Fintype.ofFinite (J ⧸ I.subgroupOf J)`. Establish `key : ∀ q : G ⧸ I, F (Quotient.out q) = F (Quotient.out (Subgroup.quotientEquivProdOfLE hIJ q).1)`. Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`.

Consider the case `H g`. Rewrite using `[UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.out_mk I F (fun a ha ↦ hF a (hIJ ha))]`. Conclude with `(UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.out_mk J F hF g).symm`. Rewrite using `[finsum_congr key, finsum_comp_equiv (Subgroup.quotientEquivProdOfLE hIJ) (f := fun p ↦ F (Quotient.out p.1)), finsum_curry _ ((hs.prod Set.finite_univ).subset (fun p hp ↦ ⟨hp, trivial⟩)), smul_finsum' _ hs]`. Use `finsum_congr fun q ↦ ?_` and prove the remaining obligations.

Rewrite using `[finsum_eq_sum_of_fintype]`. Simplify using `[Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]`.
-/
private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.finsum_le {G M : Type} [Group G] [AddCommMonoid M] {I J : Subgroup G}
    (hIJ : I ≤ J) (hne : I.relIndex J ≠ 0) (F : G → M) (hF : ∀ a ∈ J, ∀ y, F (y * a) = F y)
    (hs : (Function.support fun q : G ⧸ J ↦ F (Quotient.out q)).Finite) :
    ∑ᶠ q : G ⧸ I, F (Quotient.out q) = I.relIndex J • ∑ᶠ q : G ⧸ J, F (Quotient.out q) := by
  haveI : Finite (J ⧸ I.subgroupOf J) := Nat.finite_of_card_ne_zero hne
  haveI := Fintype.ofFinite (J ⧸ I.subgroupOf J)
  have key : ∀ q : G ⧸ I, F (Quotient.out q) =
      F (Quotient.out (Subgroup.quotientEquivProdOfLE hIJ q).1) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.out_mk I F (fun a ha ↦ hF a (hIJ ha))]
      exact (UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.out_mk J F hF g).symm
  rw [finsum_congr key, finsum_comp_equiv (Subgroup.quotientEquivProdOfLE hIJ)
    (f := fun p ↦ F (Quotient.out p.1)), finsum_curry _
      ((hs.prod Set.finite_univ).subset (fun p hp ↦ ⟨hp, trivial⟩)), smul_finsum' _ hs]
  refine finsum_congr fun q ↦ ?_
  rw [finsum_eq_sum_of_fintype]
  simp [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

/- English proof (translation)
Introduce `a ha y`. Rewrite using `[hf a ha, map_mul, Module.End.mul_apply, (UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.mem_fixed ρ H v).1 hv a ha]`.
-/
private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.term_inv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) (f : G → ℂ) (hf : ∀ a ∈ H, ∀ y, f (y * a) = f y)
    {v : V} (hv : v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ H) :
    ∀ a ∈ H, ∀ y, f (y * a) • ρ (y * a) v = f y • ρ y v := by
  intro a ha y
  rw [hf a ha, map_mul, Module.End.mul_apply, (UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.mem_fixed ρ H v).1 hv a ha]

/- English proof (translation)
Unfold `UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp`. Rewrite using `[LinearMap.smul_apply]`. Use `congr 1`. Conclude with `(LinearMap.applyₗ (R := ℂ) (M₂ := V) v).toAddMonoidHom.map_finsum (hs.subset fun q hq h0 ↦ hq (by simp only [show f (Quotient.out q) = 0 from h0, zero_smul]))`.
-/
private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_apply {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K H : Subgroup G) (f : G → ℂ)
    (hs : (Function.support fun q : G ⧸ H ↦ f (Quotient.out q)).Finite) (v : V) :
    UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K H f LinearMap.id v =
      (H.relIndex K : ℂ)⁻¹ • ∑ᶠ q : G ⧸ H, f (Quotient.out q) • ρ (Quotient.out q) v := by
  unfold UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp
  rw [LinearMap.smul_apply]
  congr 1
  exact (LinearMap.applyₗ (R := ℂ) (M₂ := V) v).toAddMonoidHom.map_finsum
    (hs.subset fun q hq h0 ↦ hq (by simp only [show f (Quotient.out q) = 0 from h0, zero_smul]))

/- English proof (translation)
Introduce `v hv`. Rewrite using `[UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_apply ρ K H f hs]`. Use `Submodule.smul_mem _ _ ((UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.mem_fixed ρ J _).2 fun a ha ↦ ?_)` and prove the remaining obligations. Establish `h1` using `(ρ a).toAddMonoidHom.map_finsum (f := fun q : G ⧸ H ↦ f (Quotient.out q) • ρ (Quotient.out q) v) (hs.subset (Function.support_smul_subset_left _ _))`. Use `h1.trans ?_` and prove the remaining obligations.

Rewrite using `[← finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ H)) (f := fun q : G ⧸ H ↦ f (Quotient.out q) • ρ (Quotient.out q) v)]`. Use `finsum_congr fun q ↦ ?_` and prove the remaining obligations. Rewrite using `[MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.out_mk H (fun g ↦ f g • ρ g v) (UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.term_inv ρ H f hr hv)]`. Simplify using `[hl a ha]`.
-/
private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_mem {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K H J : Subgroup G) (f : G → ℂ)
    (hs : (Function.support fun q : G ⧸ H ↦ f (Quotient.out q)).Finite)
    (hr : ∀ a ∈ H, ∀ y, f (y * a) = f y) (hl : ∀ a ∈ J, ∀ y, f (a * y) = f y) :
    ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ H,
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K H f LinearMap.id v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J := by
  intro v hv
  rw [UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_apply ρ K H f hs]
  refine Submodule.smul_mem _ _ ((UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.mem_fixed ρ J _).2 fun a ha ↦ ?_)
  have h1 := (ρ a).toAddMonoidHom.map_finsum
    (f := fun q : G ⧸ H ↦ f (Quotient.out q) • ρ (Quotient.out q) v)
    (hs.subset (Function.support_smul_subset_left _ _))
  refine h1.trans ?_
  rw [← finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ H))
    (f := fun q : G ⧸ H ↦ f (Quotient.out q) • ρ (Quotient.out q) v)]
  refine finsum_congr fun q ↦ ?_
  rw [MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out,
    UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.out_mk H (fun g ↦ f g • ρ g v) (UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.term_inv ρ H f hr hv)]
  simp [hl a ha]

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ P := Submodule.finiteDimensional_of_le hle`. Conclude with `LinearMap.trace_comp_comm' (Submodule.inclusion hle) (T.restrict h)`.
-/
private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trace_le {V : Type} [AddCommGroup V] [Module ℂ V]
    {P Q : Submodule ℂ V} [FiniteDimensional ℂ Q] (hle : P ≤ Q) (T : V →ₗ[ℂ] V)
    (h : ∀ v ∈ Q, T v ∈ P) :
    LinearMap.trace ℂ P (T.restrict fun v hv ↦ h v (hle hv)) =
      LinearMap.trace ℂ Q (T.restrict fun v hv ↦ hle (h v hv)) := by
  haveI : FiniteDimensional ℂ P := Submodule.finiteDimensional_of_le hle
  exact LinearMap.trace_comp_comm' (Submodule.inclusion hle) (T.restrict h)

/- English proof (translation)
Introduce `G V _ _ _ _ _ ρ K I hKo hKc hIo hIc hIK x f hf hfd`. Establish `hr : ∀ a ∈ I, ∀ y, f (y * a) = f y`. Introduce `a ha y`. Rewrite using `[hf, hf]`. Use `if_congr ⟨?_, ?_⟩ rfl rfl` and prove the remaining obligations.

Introduce and unpack `⟨c, hc, b, hb, h⟩`. Conclude with `⟨c, hc, b * a⁻¹, I.mul_mem hb (I.inv_mem ha), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩`. Introduce and unpack `⟨c, hc, b, hb, h⟩`. Conclude with `⟨c, hc, b * a, I.mul_mem hb ha, by rw [← mul_assoc, ← h]⟩`. Establish `hl : ∀ a ∈ I, ∀ y, f (a * y) = f y`.

Introduce `a ha y`. Rewrite using `[hf, hf]`. Use `if_congr ⟨?_, ?_⟩ rfl rfl` and prove the remaining obligations. Introduce and unpack `⟨c, hc, b, hb, h⟩`. Use `⟨a⁻¹ * c, I.mul_mem (I.inv_mem ha) hc, b, hb, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_assoc a⁻¹, mul_assoc a⁻¹, ← h, inv_mul_cancel_left]`. Introduce and unpack `⟨c, hc, b, hb, h⟩`. Use `⟨a * c, I.mul_mem ha hc, b, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[h, mul_assoc a, mul_assoc a]`. Establish `hC : IsCompact ((fun p : G × G ↦ p.1 * x * p.2) '' ((I : Set G) ×ˢ (I : Set G)))` using `(hIc.prod hIc).image (by fun_prop)`.

Establish `hsupp : ∀ y, f y ≠ 0 → y ∈ ((fun p : G × G ↦ p.1 * x * p.2) '' ((I : Set G) ×ˢ (I : Set G)))`. Introduce `y hy`. Rewrite `hy` using `[hf]`. Use `split_ifs at hy with h`. Take `⟨a, ha, b, hb, h⟩` from `h`.

Conclude with `⟨(a, b), ⟨ha, hb⟩, h.symm⟩`. Conclude with `absurd rfl hy`. Unfold `UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trc`. Use `set J : Subgroup G := K ⊓ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.rStab f ⊓ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.rStab fun (y : G) ↦ f y⁻¹ with hJ`. Establish `hIJ : I ≤ J`.

Introduce `a ha`. Use `⟨⟨hIK ha, fun y ↦ hr a ha y⟩, fun y ↦ ?_⟩` and prove the remaining obligations. Use `show f (y * a)⁻¹ = f y⁻¹`. Rewrite using `[mul_inv_rev, hl _ (I.inv_mem ha)]`. Establish `hJK : J ≤ K` using `fun a ha ↦ ha.1.1`.

Establish `hJr : ∀ a ∈ J, ∀ y, f (y * a) = f y` using `fun a ha y ↦ ha.1.2 y`. Establish `hJl : ∀ a ∈ J, ∀ y, f (a * y) = f y`. Introduce `a ha y`. Establish `h : f (y⁻¹ * a⁻¹)⁻¹ = f y⁻¹⁻¹` using `(J.inv_mem ha).2 y⁻¹`. Simplify using `using h`.

Establish `hJo : IsOpen (J : Set G)` using `Subgroup.isOpen_mono hIJ hIo`. Establish `hsI` using `UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.supp_finite I hIo hC f hsupp`. Establish `hsJ` using `UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.supp_finite J hJo hC f hsupp`. Establish `hne : I.relIndex K ≠ 0` using `UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.relIndex_ne K I hKc hIo`. Establish `hmul : I.relIndex J * J.relIndex K = I.relIndex K` using `Subgroup.relIndex_mul_relIndex I J K hIJ hJK`.

Establish `hne1 : I.relIndex J ≠ 0` using `left_ne_zero_of_mul (hmul ▸ hne)`. Establish `hle : UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J ≤ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I`. Introduce `v hv`. Rewrite `hv`, the goal using `[UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.mem_fixed]`. Conclude with `fun a ha ↦ hv a (hIJ ha)`.

Establish `h1 : ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I, UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K I f LinearMap.id v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J` using `UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_mem ρ K I J f hsI hr hJl`. Establish `h2 : ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J, UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K J f LinearMap.id v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J` using `UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_mem ρ K J J f hsJ hJr hJl`. Establish `h3 : ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I, UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K I f LinearMap.id v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I` using `fun v hv ↦ hle (h1 v hv)`. Establish `h4 : ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J, UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K I f LinearMap.id v = UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K J f LinearMap.id v`. Introduce `v hv`.

Rewrite using `[UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_apply ρ K I f hsI, UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_apply ρ K J f hsJ, UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.finsum_le hIJ hne1 (fun g ↦ f g • ρ g v) (UpperTheor …`. Use `congr 1`. Establish `: (I.relIndex J : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hne1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Unfold `UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.twTr`. Rewrite using `[dif_pos h2, dif_pos h3, ← UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trace_le hle _ h1]`. Use `congr 1`. Use extensionality with `v`. Conclude with `(h4 v v.2).symm`.
-/
theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trc_eq :
    ∀ {G V : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (K I : Subgroup G),
      IsOpen (↑K : Set G) →
        IsCompact (↑K : Set G) →
          IsOpen (↑I : Set G) →
            IsCompact (↑I : Set G) →
              I ≤ K →
                ∀ (x : G) (f : G → ℂ),
                  (∀ (y : G), f y = if ∃ a ∈ I, ∃ b ∈ I, y = a * x * b then (1 : ℂ) else (0 : ℂ)) →
                    FiniteDimensional ℂ ↥(UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I) →
                      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trc ρ K f = UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.twTr ρ K I f LinearMap.id := by
  intro G V _ _ _ _ _ ρ K I hKo hKc hIo hIc hIK x f hf hfd
  have hr : ∀ a ∈ I, ∀ y, f (y * a) = f y := by
    intro a ha y
    rw [hf, hf]
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro ⟨c, hc, b, hb, h⟩
      exact ⟨c, hc, b * a⁻¹, I.mul_mem hb (I.inv_mem ha), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
    · rintro ⟨c, hc, b, hb, h⟩
      exact ⟨c, hc, b * a, I.mul_mem hb ha, by rw [← mul_assoc, ← h]⟩
  have hl : ∀ a ∈ I, ∀ y, f (a * y) = f y := by
    intro a ha y
    rw [hf, hf]
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro ⟨c, hc, b, hb, h⟩
      refine ⟨a⁻¹ * c, I.mul_mem (I.inv_mem ha) hc, b, hb, ?_⟩
      rw [mul_assoc a⁻¹, mul_assoc a⁻¹, ← h, inv_mul_cancel_left]
    · rintro ⟨c, hc, b, hb, h⟩
      refine ⟨a * c, I.mul_mem ha hc, b, hb, ?_⟩
      rw [h, mul_assoc a, mul_assoc a]
  have hC : IsCompact ((fun p : G × G ↦ p.1 * x * p.2) '' ((I : Set G) ×ˢ (I : Set G))) :=
    (hIc.prod hIc).image (by fun_prop)
  have hsupp : ∀ y, f y ≠ 0 → y ∈ ((fun p : G × G ↦ p.1 * x * p.2) '' ((I : Set G) ×ˢ (I : Set G))) := by
    intro y hy
    rw [hf] at hy
    split_ifs at hy with h
    · obtain ⟨a, ha, b, hb, h⟩ := h
      exact ⟨(a, b), ⟨ha, hb⟩, h.symm⟩
    · exact absurd rfl hy
  unfold UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trc
  set J : Subgroup G := K ⊓ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.rStab f ⊓ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.rStab fun (y : G) ↦ f y⁻¹ with hJ
  have hIJ : I ≤ J := by
    intro a ha
    refine ⟨⟨hIK ha, fun y ↦ hr a ha y⟩, fun y ↦ ?_⟩
    show f (y * a)⁻¹ = f y⁻¹
    rw [mul_inv_rev, hl _ (I.inv_mem ha)]
  have hJK : J ≤ K := fun a ha ↦ ha.1.1
  have hJr : ∀ a ∈ J, ∀ y, f (y * a) = f y := fun a ha y ↦ ha.1.2 y
  have hJl : ∀ a ∈ J, ∀ y, f (a * y) = f y := by
    intro a ha y
    have h : f (y⁻¹ * a⁻¹)⁻¹ = f y⁻¹⁻¹ := (J.inv_mem ha).2 y⁻¹
    simpa using h
  have hJo : IsOpen (J : Set G) := Subgroup.isOpen_mono hIJ hIo
  have hsI := UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.supp_finite I hIo hC f hsupp
  have hsJ := UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.supp_finite J hJo hC f hsupp
  have hne : I.relIndex K ≠ 0 := UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.relIndex_ne K I hKc hIo
  have hmul : I.relIndex J * J.relIndex K = I.relIndex K := Subgroup.relIndex_mul_relIndex I J K hIJ hJK
  have hne1 : I.relIndex J ≠ 0 := left_ne_zero_of_mul (hmul ▸ hne)
  have hle : UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J ≤ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I := by
    intro v hv
    rw [UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.mem_fixed] at hv ⊢
    exact fun a ha ↦ hv a (hIJ ha)
  have h1 : ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I,
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K I f LinearMap.id v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J :=
    UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_mem ρ K I J f hsI hr hJl
  have h2 : ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J,
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K J f LinearMap.id v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J :=
    UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_mem ρ K J J f hsJ hJr hJl
  have h3 : ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I,
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K I f LinearMap.id v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I :=
    fun v hv ↦ hle (h1 v hv)
  have h4 : ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J,
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K I f LinearMap.id v = UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K J f LinearMap.id v := by
    intro v hv
    rw [UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_apply ρ K I f hsI, UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_apply ρ K J f hsJ,
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.finsum_le hIJ hne1 (fun g ↦ f g • ρ g v)
        (UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.term_inv ρ J f hJr hv)
        (hsJ.subset (Function.support_smul_subset_left _ _)), ← hmul,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    have : (I.relIndex J : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne1
    push_cast
    field_simp
  unfold UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.twTr
  rw [dif_pos h2, dif_pos h3, ← UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trace_le hle _ h1]
  congr 1
  ext v
  exact (h4 v v.2).symm
