import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

/- English proof (translation)
Introduce `G V _ _ _ _ _ π hπ H θ hD w`. Set `Hs : Subgroup G` to `{ carrier := H mul_mem' := fun {a b} ha hb => hD.mul a ha b hb one_mem' := hD.one inv_mem' := fun {a} ha => hD.inv a ha }`. Establish `hθinv : ∀ a ∈ H, θ a⁻¹ * θ a = 1` using `fun a ha => by`. Rewrite using `[← hD.val_mul _ (hD.inv a ha) _ ha, inv_mul_cancel, hD.val_one]`. Establish `hθ0 : ∀ a ∈ H, θ a ≠ 0` using `fun a ha h0 => by`.

Use `hθinv a ha` as an intermediate fact. Rewrite `this` using `[h0, mul_zero]`. Conclude with `zero_ne_one this`. Establish `hπmul : ∀ a b : G, π (a * b) w = π a (π b w)` using `fun a b => by rw [map_mul]; rfl`. Set `T : Subgroup Hs` to `{ carrier := {j | π j w = θ j • w} one_mem' := by simp [hD.val_one] mul_mem' := fun {a b} ha hb => by`.

Simplify using `only [Set.mem_setOf_eq, Subgroup.coe_mul] at ha hb ⊢`. Rewrite using `[hπmul, hb, map_smul, ha, smul_smul, hD.val_mul _ a.2 _ b.2, mul_comm]`. Use the proof step `inv_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_setOf_eq, InvMemClass.coe_inv] at ha ⊢`. Establish `h1 : w = θ a • π (a : G)⁻¹ w`.

Rewrite using `[← map_smul, ← ha, ← hπmul, inv_mul_cancel, map_one]`. Both sides reduce to the same expression. Establish `h2 : θ (a : G)⁻¹ = (θ a)⁻¹` using `eq_inv_of_mul_eq_one_left (hθinv a a.2)`. Rewrite using `[h2]`. Use `conv_rhs => rw [h1]`.

Rewrite using `[smul_smul, inv_mul_cancel₀ (hθ0 a a.2), one_smul] }`. Use `haveI : CompactSpace Hs := isCompact_iff_compactSpace.mp hD.compact`. Establish `hopen : IsOpen (T : Set Hs)`. Apply `Subgroup.isOpen_of_mem_nhds T (g := 1)` to reduce the goal to its premises. Rewrite using `[nhds_subtype_eq_comap, Filter.mem_comap]`.

Take `⟨U, hU, hUθ⟩` from `hD.near`. Use `⟨U ∩ {g | π g w = w}, Filter.inter_mem hU ((hπ w).mem_nhds (by simp)), ?_⟩` and prove the remaining obligations. Introduce and unpack `j ⟨hjU, hjw⟩`. Use `show π j w = θ j • w`. Rewrite using `[hjw, hUθ _ hjU j.2, one_smul]`.

Use `haveI : Finite (Hs ⧸ T) := Subgroup.quotient_finite_of_isOpen T hopen`. Use `haveI : Fintype (Hs ⧸ T) := Fintype.ofFinite _`. Set `f : Hs → V` to `fun j => (θ j)⁻¹ • π j w`. Establish `hf : ∀ a b : Hs, (a : Hs ⧸ T) = b → f a = f b`. Introduce `a b hab`.

Rewrite `hab` using `[QuotientGroup.eq]`. Establish `hb : b = a * (a⁻¹ * b)` using `by group`. Generalize the expression as in `a⁻¹ * b = s at hab hb`. Substitute `hb` using the available equality. Establish `hs : π s w = θ s • w` using `hab`.

Simplify using `only [f, Subgroup.coe_mul]`. Rewrite using `[hπmul, hs, map_smul, smul_smul, hD.val_mul _ a.2 _ s.2, mul_inv, mul_assoc, inv_mul_cancel₀ (hθ0 s s.2), mul_one]`. Establish `hact : ∀ h a : Hs, π h (f a) = θ h • f (h * a)`. Introduce `h a`. Simplify using `only [f, Subgroup.coe_mul]`.

Rewrite using `[map_smul, hπmul, smul_smul, hD.val_mul _ h.2 _ a.2, mul_inv, ← mul_assoc, mul_inv_cancel₀ (hθ0 h h.2), one_mul]`. Set `rep : Hs ⧸ T → Hs` to `fun q => if q = ((1 : Hs) : Hs ⧸ T) then 1 else q.out`. Establish `hrep : ∀ q, ((rep q : Hs) : Hs ⧸ T) = q`. Introduce `q`. Simplify using `only [rep]`.

Use `split_ifs with hq`. Conclude with `hq.symm`. Conclude with `QuotientGroup.out_eq' q`. Establish `hsum : ∀ h : Hs, π h (∑ q, f (rep q)) = θ h • ∑ q, f (rep q)`. Introduce `h`.

Rewrite using `[map_sum, Finset.smul_sum]`. Repeatedly rewrite using `[hact]`. Establish `: ∀ q, f (h * rep q) = f (rep (h • q))` using `fun q => by`. Apply `hf` to reduce the goal to its premises. Rewrite using `[hrep (h • q)]`.

Use `conv_rhs => rw [← hrep q]`. Rewrite using `[MulAction.Quotient.smul_mk, smul_eq_mul]`. Repeatedly rewrite using `[this]`. Conclude with `Equiv.sum_comp (MulAction.toPerm h) (fun q => θ h • f (rep q))`. Use `⟨Finset.univ.image (fun q => ((rep q : Hs) : G)), ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `Finset.mem_image.mpr ⟨((1 : Hs) : Hs ⧸ T), Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Simplify using `[rep]`. Introduce `j hj`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.mp hj`. Conclude with `(rep q).2`.

Establish `hinj : Set.InjOn (fun q => ((rep q : Hs) : G)) (Finset.univ : Finset (Hs ⧸ T))`. Introduce `q₁ _ q₂ _ h`. Rewrite using `[← hrep q₁, ← hrep q₂, Subtype.ext h]`. Rewrite using `[Finset.sum_image hinj]`. Introduce `h hh`.

Conclude with `hsum ⟨h, hh⟩`.
-/
theorem avg_eig : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ w : V,
    ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ IsEig π H θ (∑ j ∈ R, (θ j)⁻¹ • π j w) := by
  intro G V _ _ _ _ _ π hπ H θ hD w
  classical
  let Hs : Subgroup G :=
    { carrier := H
      mul_mem' := fun {a b} ha hb => hD.mul a ha b hb
      one_mem' := hD.one
      inv_mem' := fun {a} ha => hD.inv a ha }
  have hθinv : ∀ a ∈ H, θ a⁻¹ * θ a = 1 := fun a ha => by
    rw [← hD.val_mul _ (hD.inv a ha) _ ha, inv_mul_cancel, hD.val_one]
  have hθ0 : ∀ a ∈ H, θ a ≠ 0 := fun a ha h0 => by
    have := hθinv a ha; rw [h0, mul_zero] at this; exact zero_ne_one this
  have hπmul : ∀ a b : G, π (a * b) w = π a (π b w) := fun a b => by rw [map_mul]; rfl
  let T : Subgroup Hs :=
    { carrier := {j | π j w = θ j • w}
      one_mem' := by simp [hD.val_one]
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul] at ha hb ⊢
        rw [hπmul, hb, map_smul, ha, smul_smul, hD.val_mul _ a.2 _ b.2, mul_comm]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, InvMemClass.coe_inv] at ha ⊢
        have h1 : w = θ a • π (a : G)⁻¹ w := by
          rw [← map_smul, ← ha, ← hπmul, inv_mul_cancel, map_one]; rfl
        have h2 : θ (a : G)⁻¹ = (θ a)⁻¹ := eq_inv_of_mul_eq_one_left (hθinv a a.2)
        rw [h2]
        conv_rhs => rw [h1]
        rw [smul_smul, inv_mul_cancel₀ (hθ0 a a.2), one_smul] }
  haveI : CompactSpace Hs := isCompact_iff_compactSpace.mp hD.compact
  have hopen : IsOpen (T : Set Hs) := by
    apply Subgroup.isOpen_of_mem_nhds T (g := 1)
    rw [nhds_subtype_eq_comap, Filter.mem_comap]
    obtain ⟨U, hU, hUθ⟩ := hD.near
    refine ⟨U ∩ {g | π g w = w}, Filter.inter_mem hU ((hπ w).mem_nhds (by simp)), ?_⟩
    rintro j ⟨hjU, hjw⟩
    show π j w = θ j • w
    rw [hjw, hUθ _ hjU j.2, one_smul]
  haveI : Finite (Hs ⧸ T) := Subgroup.quotient_finite_of_isOpen T hopen
  haveI : Fintype (Hs ⧸ T) := Fintype.ofFinite _
  let f : Hs → V := fun j => (θ j)⁻¹ • π j w
  have hf : ∀ a b : Hs, (a : Hs ⧸ T) = b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.eq] at hab
    have hb : b = a * (a⁻¹ * b) := by group
    generalize a⁻¹ * b = s at hab hb
    subst hb
    have hs : π s w = θ s • w := hab
    simp only [f, Subgroup.coe_mul]
    rw [hπmul, hs, map_smul, smul_smul, hD.val_mul _ a.2 _ s.2, mul_inv, mul_assoc,
      inv_mul_cancel₀ (hθ0 s s.2), mul_one]
  have hact : ∀ h a : Hs, π h (f a) = θ h • f (h * a) := by
    intro h a
    simp only [f, Subgroup.coe_mul]
    rw [map_smul, hπmul, smul_smul, hD.val_mul _ h.2 _ a.2, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (hθ0 h h.2), one_mul]
  let rep : Hs ⧸ T → Hs := fun q => if q = ((1 : Hs) : Hs ⧸ T) then 1 else q.out
  have hrep : ∀ q, ((rep q : Hs) : Hs ⧸ T) = q := by
    intro q
    simp only [rep]
    split_ifs with hq
    · exact hq.symm
    · exact QuotientGroup.out_eq' q
  have hsum : ∀ h : Hs, π h (∑ q, f (rep q)) = θ h • ∑ q, f (rep q) := by
    intro h
    rw [map_sum, Finset.smul_sum]
    simp_rw [hact]
    have : ∀ q, f (h * rep q) = f (rep (h • q)) := fun q => by
      apply hf
      rw [hrep (h • q)]
      conv_rhs => rw [← hrep q]
      rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    simp_rw [this]
    exact Equiv.sum_comp (MulAction.toPerm h) (fun q => θ h • f (rep q))
  refine ⟨Finset.univ.image (fun q => ((rep q : Hs) : G)), ?_, ?_, ?_⟩
  · refine Finset.mem_image.mpr ⟨((1 : Hs) : Hs ⧸ T), Finset.mem_univ _, ?_⟩
    simp [rep]
  · intro j hj
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hj
    exact (rep q).2
  · have hinj : Set.InjOn (fun q => ((rep q : Hs) : G)) (Finset.univ : Finset (Hs ⧸ T)) := by
      intro q₁ _ q₂ _ h
      rw [← hrep q₁, ← hrep q₂, Subtype.ext h]
    rw [Finset.sum_image hinj]
    intro h hh
    exact hsum ⟨h, hh⟩

end GlobalTheory.PsType
