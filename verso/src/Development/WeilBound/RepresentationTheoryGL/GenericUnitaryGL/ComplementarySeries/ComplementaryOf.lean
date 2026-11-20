import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SesquilinearFlipConj

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace PositivityTheory.RgGu.NR

namespace Compl

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
The claim follows from `(eq_bot_or_eq_top (⟨W, hW⟩ : Subrepresentation ρ)).imp (congrArg Subrepresentation.toSubmodule) (congrArg Subrepresentation.toSubmodule)`.
-/
theorem irr_sub {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  (eq_bot_or_eq_top (⟨W, hW⟩ : Subrepresentation ρ)).imp (congrArg Subrepresentation.toSubmodule)
    (congrArg Subrepresentation.toSubmodule)

/- English proof (translation)
Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nontrivial_iff_subsingleton]`. Establish `: (⊥ : Subrepresentation ρ) = ⊤` using `Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)`. Conclude with `bot_ne_top this`.
-/
theorem irr_nontrivial {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
  exact bot_ne_top this

def starF {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ) :
    M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => starRingEnd ℂ (B w v))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem starF_apply {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ)
    (v w : M) : starF B v w = starRingEnd ℂ (B w v) := rfl

def resF {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ) (W : Submodule ℂ M) :
    W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => B v w)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem resF_apply {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ)
    (W : Submodule ℂ M) (v w : W) : resF B W v w = B v w := rfl

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.SesquilinearFlipConj.main h`.
-/
theorem exists_herm {ρ : Representation ℂ G V} (h : HasSesq ρ) :
    ∃ B : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ, B ≠ 0 ∧ (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧
      ∀ g v w, B (ρ g v) (ρ g w) = B v w :=
  _root_.UpperTheory.Reformulated.B.SesquilinearFlipConj.main h

def stabG (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Set `R : Submodule ℂ V` to `{ carrier := {v | ∀ x, C v x = 0} add_mem' := fun {a b} ha hb x => by simp [ha x, hb x] zero_mem' := fun x => by simp smul_mem' := fun c a ha x => by simp [ha x] }`. Establish `hR : ∀ g, ∀ y ∈ R, ρ g y ∈ R`. Introduce `g y hy x`.

Use `hCi g y (ρ g⁻¹ x)` as an intermediate fact. Rewrite `this` using `[← Module.End.mul_apply (ρ g), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite using `[this]`. Conclude with `hy _`. Break down `irr_sub hi R hR with h1 | h1` into its components or cases.

Establish `: v ∈ R` using `hcon`. Rewrite `this` using `[h1, Submodule.mem_bot]`. Conclude with `hv this`. Apply `hC0` to reduce the goal to its premises. Use extensionality with `a b`.

Establish `: a ∈ R` using `h1 ▸ Submodule.mem_top`. Simplify using `using this b`.
-/
theorem nondeg {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ) (hC0 : C ≠ 0)
    (hCi : ∀ g v w, C (ρ g v) (ρ g w) = C v w) (v : V) (hv : v ≠ 0) : ∃ x, C v x ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  let R : Submodule ℂ V :=
    { carrier := {v | ∀ x, C v x = 0}
      add_mem' := fun {a b} ha hb x => by simp [ha x, hb x]
      zero_mem' := fun x => by simp
      smul_mem' := fun c a ha x => by simp [ha x] }
  have hR : ∀ g, ∀ y ∈ R, ρ g y ∈ R := by
    intro g y hy x
    have := hCi g y (ρ g⁻¹ x)
    rw [← Module.End.mul_apply (ρ g), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    rw [this]; exact hy _
  rcases irr_sub hi R hR with h1 | h1
  · have : v ∈ R := hcon
    rw [h1, Submodule.mem_bot] at this
    exact hv this
  · apply hC0
    ext a b
    have : a ∈ R := h1 ▸ Submodule.mem_top
    simpa using this b

end Compl

open _root_.PositivityTheory.RgGu.NR.Compl in
/- English proof (translation)
Introduce `G V _ _ _ _ _ K₀ hK₀o hK₀c F hF hall h0 s hs`. Establish `hsm : IsSmooth (F 0)` using `(hall 0 le_rfl).2.1`. Establish `hirr : (F s).IsIrreducible` using `(hall s hs).2.2.1`. Use `haveI := irr_nontrivial hirr`. Take `⟨H, hH0, hHh, hHi⟩` from `exists_herm (hall s hs).2.2.2`.

Take `⟨B₀, hB₀h, hB₀p, hB₀i⟩` from `h0`. Establish `key : ∀ K : Subgroup G, IsOpen (K : Set G) → K ≤ K₀ → fixed (F 0) K ≠ ⊥ → (∀ w ∈ fixed (F 0) K, w ≠ 0 → 0 < (H w w).re) ∨ (∀ w ∈ fixed (F 0) K, w ≠ 0 → (H w w).re < 0)`. Introduce `K hKo hKle hW`. Establish `hKc : IsCompact (K : Set G)` using `hK₀c.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo) hKle`. Use `set W := fixed (F 0) K with hWdef`.

Use `haveI : FiniteDimensional ℂ W := (hall 0 le_rfl).1.2 K hKo hKc`. Use `set e := idem hsm hKc with he`. Establish `hconst : ∀ t, ∀ x ∈ K, F t x = F 0 x` using `fun t x hx => hF.const t x (hKle hx)`. Establish `hker : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) → ∀ y ∈ twKer (F 0) K 1, ∀ w ∈ W, C y w = 0 ∧ C w y = 0`. Introduce `t C hC y hy w hw`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨n, u, rfl⟩` from `hx`. Establish `hn : (F 0) (n : G) w = w` using `GlobalTheory.Parabolic.mem_fixed.1 hw _ n.2`. Establish `hn' : F t (n : G) = F 0 (n : G)` using `hconst t _ n.2`.

Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, LinearMap.sub_apply]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← hn, ← hn', hC, hn', hn, sub_self]`. Rewrite using `[← hn, ← hn', hC, hn', hn, sub_self]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => simp [hx.1, hy.1, hx.2, hy.2]`. Consider the case `smul c x _ hx => simp [hx.1, hx.2]`. Establish `hsub : ∀ x : V, x - e x ∈ twKer (F 0) K 1` using `fun x => by`. Rewrite using `[← idem_eq_zero_iff hsm hKc, map_sub, idem_of_mem hsm hKc (idem_mem hsm hKc x), sub_self]`. Establish `hleft : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) → ∀ x, ∀ w ∈ W, C (e x) w = C x w ∧ C w (e x) = C w x`.

Introduce `t C hC x w hw`. Take `⟨h1, h2⟩` from `hker t C hC _ (hsub x) w hw`. Rewrite `h1` using `[map_sub, LinearMap.sub_apply, sub_eq_zero]`. Rewrite `h2` using `[map_sub, sub_eq_zero]`. Conclude with `⟨h1.symm, h2.symm⟩`.

Set `T : ℝ → G → Module.End ℂ W` to `fun t g => (e ∘ₗ (F t g) ∘ₗ W.subtype).codRestrict W (fun v => idem_mem hsm hKc _)`. Establish `hT : ∀ t g (v : W), ((T t g v : W) : V) = e (F t g v)` using `fun _ _ _ => rfl`. Establish `hinvW : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) → ∀ (g : G) (v w : W), resF C W (T t g v) w = resF C W v (T t g⁻¹ w)`. Introduce `t C hC g v w`. Simplify using `only [resF_apply, hT]`.

Rewrite using `[(hleft t C hC _ w w.2).1, (hleft t C hC _ v v.2).2]`. Use `conv_lhs => rw [← hC g⁻¹]`. Rewrite using `[← Module.End.mul_apply (F t g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Establish `hcont : ∀ (g : G) (w : W) (l : Module.Dual ℂ W), Continuous fun t => l (T t g w)`. Introduce `g w l`.

Take `⟨m, r, u, hu⟩` from `hF.expo g w`. Establish `e1 : ∀ t, T t g w = ∑ i, ((Real.exp (r i * t) : ℝ) : ℂ) • (⟨e (u i), idem_mem hsm hKc _⟩ : W)`. Introduce `t`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hT, hu t, map_sum, Submodule.coe_sum]`.

Simplify using `only [map_smul, Submodule.coe_smul]`. Repeatedly rewrite using `[e1, map_sum, map_smul, smul_eq_mul]`. Use `continuous_finset_sum _ fun i _ => Continuous.mul ?_ continuous_const` and prove the remaining obligations. Conclude with `Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))`. Establish `hsimple : ∀ t, 0 ≤ t → ∀ U : Submodule ℂ W, (∀ g, ∀ w ∈ U, T t g w ∈ U) → U = ⊥ ∨ U = ⊤`.

Introduce `t ht U hU`. Distinguish the cases in `hU0 : U = ⊥`. Conclude with `Or.inl hU0`. Use `right`. Take `⟨u, huU, hu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hU0`.

Set `S : Submodule ℂ V` to `Submodule.span ℂ (Set.range fun g => F t g u)`. Establish `hS : ∀ g, ∀ x ∈ S, F t g x ∈ S`. Introduce `g x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨g', rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨g * g', by simp only [map_mul, Module.End.mul_apply]⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `S.add_mem hx hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `S.smul_mem c hx`. Establish `hSt : S = ⊤`. Break down `irr_sub (hall t ht).2.2.1 S hS with h1 | h1` into its components or cases. It suffices to derive a contradiction.

Apply `hu0` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Establish `: ((u : W) : V) ∈ S` using `Submodule.subset_span ⟨1, by simp⟩`. Rewrite `this` using `[h1, Submodule.mem_bot]`. Simplify using `using this`.

Conclude with `h1`. Establish `hmem : ∀ x ∈ S, (⟨e x, idem_mem hsm hKc x⟩ : W) ∈ U`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨g, rfl⟩` from `hy`. Conclude with `hU g u huU`. Consider the case `zero`. Use `U.zero_mem using 1` and compare the differences between its conclusion and the goal. Conclude with `Subtype.ext (by simp)`.

Consider the case `add x y _ _ hx hy`. Establish `: (⟨e (x + y), idem_mem hsm hKc _⟩ : W) = ⟨e x, idem_mem hsm hKc _⟩ + ⟨e y, idem_mem hsm hKc _⟩` using `Subtype.ext (by simp)`. Rewrite using `[this]`. Conclude with `U.add_mem hx hy`. Consider the case `smul c x _ hx`.

Establish `: (⟨e (c • x), idem_mem hsm hKc _⟩ : W) = c • ⟨e x, idem_mem hsm hKc _⟩` using `Subtype.ext (by simp)`. Rewrite using `[this]`. Conclude with `U.smul_mem c hx`. Use `eq_top_iff.2 fun w _ => ?_` and prove the remaining obligations. Establish `hw : (⟨e w, idem_mem hsm hKc _⟩ : W) = w` using `Subtype.ext (idem_of_mem hsm hKc w.2)`.

Rewrite using `[← hw]`. Conclude with `hmem w (hSt ▸ Submodule.mem_top)`. Use `haveI : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).2 hW`. Establish `hresne : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) → (F t).IsIrreducible → C ≠ 0 → resF C W ≠ 0`. Introduce `t C hCi hi hC0 h0'`.

Take `⟨w, hw0⟩` from `exists_ne (0 : W)`. Take `⟨x, hx⟩` from `nondeg hi C hC0 hCi w (fun e0 => hw0 (Subtype.ext e0))`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← (hleft t C hCi x w w.2).2]`. Use `congrArg (fun f => f w ⟨e x, idem_mem hsm hKc x⟩) h0'` as an intermediate fact.

Simplify using `using this`. Establish `hforms : ∀ t, 0 ≤ t → ∃ C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ, C ≠ 0 ∧ (∀ v w, C w v = starRingEnd ℂ (C v w)) ∧ ∀ g v w, C (T t g v) w = C v (T t g⁻¹ w)`. Introduce `t ht`. Take `⟨C, hC0, hCh, hCi⟩` from `exists_herm (hall t ht).2.2.2`. Conclude with `⟨resF C W, hresne t C hCi (hall t ht).2.2.1 hC0, fun v w => hCh v w, hinvW t C hCi⟩`.

Establish `hpos0 : ∃ C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ, (∀ v w, C w v = starRingEnd ℂ (C v w)) ∧ (∀ v, v ≠ 0 → 0 < (C v v).re) ∧ ∀ g v w, C (T 0 g v) w = C v (T 0 g⁻¹ w)` using `⟨resF B₀ W, fun v w => hB₀h v w, fun v hv => hB₀p v (fun e0 => hv (Subtype.ext e0)), hinvW 0 B₀ hB₀i⟩`. Break down `h G W (fun g => g⁻¹) T (fun i w l => hcont i w l) hsimple hforms hpos0 inv_surjective s hs (resF H W) (hresne s H hHi hirr hH0) (fun v w => hHh v w) (hinvW s H hHi) with h1 | h1` into its components or cases. Conclude with `Or.inl fun w hw hw0 => h1 ⟨w, hw⟩ (fun e0 => hw0 (congrArg Subtype.val e0))`. Conclude with `Or.inr fun w hw hw0 => h1 ⟨w, hw⟩ (fun e0 => hw0 (congrArg Subtype.val e0))`. Take `⟨v₁, hv₁⟩` from `exists_ne (0 : V)`.

Establish `hopen : ∀ v : V, IsOpen ((stabG (F 0) v : Subgroup G) : Set G)` using `fun v => hsm v`. Set `K₁ : Subgroup G` to `K₀ ⊓ stabG (F 0) v₁`. Establish `hK₁o : IsOpen (K₁ : Set G)` using `hK₀o.inter (hopen v₁)`. Establish `hv₁K : ∀ K : Subgroup G, K ≤ K₁ → v₁ ∈ fixed (F 0) K` using `fun K hK => GlobalTheory.Parabolic.mem_fixed.2 fun g hg => (hK hg).2`. Establish `hne : ∀ K : Subgroup G, K ≤ K₁ → fixed (F 0) K ≠ ⊥` using `fun K hK h' => by`.

Use `hv₁K K hK` as an intermediate fact. Rewrite `this` using `[h', Submodule.mem_bot]`. Conclude with `hv₁ this`. Establish `hloc : ∀ v : V, v ≠ 0 → ((0 < (H v₁ v₁).re → 0 < (H v v).re) ∧ ((H v₁ v₁).re < 0 → (H v v).re < 0))`. Introduce `v hv`.

Set `Kv : Subgroup G` to `K₁ ⊓ stabG (F 0) v`. Establish `hKvo : IsOpen (Kv : Set G)` using `hK₁o.inter (hopen v)`. Establish `hvK : v ∈ fixed (F 0) Kv` using `GlobalTheory.Parabolic.mem_fixed.2 fun g hg => hg.2`. Break down `key Kv hKvo (inf_le_left.trans inf_le_left) (hne Kv inf_le_left) with h1 | h1` into its components or cases. Establish `a` using `h1 v hvK hv`.

Establish `b` using `h1 v₁ (hv₁K Kv inf_le_left) hv₁`. Conclude with `⟨fun _ => a, fun hb => absurd b (not_lt.2 hb.le)⟩`. Establish `a` using `h1 v hvK hv`. Establish `b` using `h1 v₁ (hv₁K Kv inf_le_left) hv₁`. Conclude with `⟨fun hb => absurd b (not_lt.2 hb.le), fun _ => a⟩`.

Break down `key K₁ hK₁o inf_le_left (hne K₁ le_rfl) with h1 | h1` into its components or cases. Establish `hp` using `h1 v₁ (hv₁K K₁ le_rfl) hv₁`. Conclude with `⟨H, fun v w => hHh v w, fun v hv => (hloc v hv).1 hp, hHi⟩`. Establish `hn` using `h1 v₁ (hv₁K K₁ le_rfl) hv₁`. Use `⟨-H, fun v w => ?_, fun v hv => ?_, fun g v w => ?_⟩` and prove the remaining obligations.

Simplify using `[hHh v w]`. Use `(hloc v hv).2 hn` as an intermediate fact. Simplify using `only [LinearMap.neg_apply, Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[hHi]`.
-/
theorem complementary_of (h : Signature) : Complementary := by
  intro G V _ _ _ _ _ K₀ hK₀o hK₀c F hF hall h0 s hs
  have hsm : IsSmooth (F 0) := (hall 0 le_rfl).2.1
  have hirr : (F s).IsIrreducible := (hall s hs).2.2.1
  haveI := irr_nontrivial hirr
  obtain ⟨H, hH0, hHh, hHi⟩ := exists_herm (hall s hs).2.2.2
  obtain ⟨B₀, hB₀h, hB₀p, hB₀i⟩ := h0
  have key : ∀ K : Subgroup G, IsOpen (K : Set G) → K ≤ K₀ → fixed (F 0) K ≠ ⊥ →
      (∀ w ∈ fixed (F 0) K, w ≠ 0 → 0 < (H w w).re) ∨ (∀ w ∈ fixed (F 0) K, w ≠ 0 → (H w w).re < 0) := by
    intro K hKo hKle hW
    have hKc : IsCompact (K : Set G) := hK₀c.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo) hKle
    set W := fixed (F 0) K with hWdef
    haveI : FiniteDimensional ℂ W := (hall 0 le_rfl).1.2 K hKo hKc
    set e := idem hsm hKc with he
    have hconst : ∀ t, ∀ x ∈ K, F t x = F 0 x := fun t x hx => hF.const t x (hKle hx)
    have hker : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) →
        ∀ y ∈ twKer (F 0) K 1, ∀ w ∈ W, C y w = 0 ∧ C w y = 0 := by
      intro t C hC y hy w hw
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, u, rfl⟩ := hx
        have hn : (F 0) (n : G) w = w := GlobalTheory.Parabolic.mem_fixed.1 hw _ n.2
        have hn' : F t (n : G) = F 0 (n : G) := hconst t _ n.2
        simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, LinearMap.sub_apply]
        constructor
        · rw [← hn, ← hn', hC, hn', hn, sub_self]
        · rw [← hn, ← hn', hC, hn', hn, sub_self]
      | zero => simp
      | add x y _ _ hx hy => simp [hx.1, hy.1, hx.2, hy.2]
      | smul c x _ hx => simp [hx.1, hx.2]
    have hsub : ∀ x : V, x - e x ∈ twKer (F 0) K 1 := fun x => by
      rw [← idem_eq_zero_iff hsm hKc, map_sub, idem_of_mem hsm hKc (idem_mem hsm hKc x), sub_self]
    have hleft : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) →
        ∀ x, ∀ w ∈ W, C (e x) w = C x w ∧ C w (e x) = C w x := by
      intro t C hC x w hw
      obtain ⟨h1, h2⟩ := hker t C hC _ (hsub x) w hw
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h1
      rw [map_sub, sub_eq_zero] at h2
      exact ⟨h1.symm, h2.symm⟩
    let T : ℝ → G → Module.End ℂ W := fun t g =>
      (e ∘ₗ (F t g) ∘ₗ W.subtype).codRestrict W (fun v => idem_mem hsm hKc _)
    have hT : ∀ t g (v : W), ((T t g v : W) : V) = e (F t g v) := fun _ _ _ => rfl
    have hinvW : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) →
        ∀ (g : G) (v w : W), resF C W (T t g v) w = resF C W v (T t g⁻¹ w) := by
      intro t C hC g v w
      simp only [resF_apply, hT]
      rw [(hleft t C hC _ w w.2).1, (hleft t C hC _ v v.2).2]
      conv_lhs => rw [← hC g⁻¹]
      rw [← Module.End.mul_apply (F t g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hcont : ∀ (g : G) (w : W) (l : Module.Dual ℂ W), Continuous fun t => l (T t g w) := by
      intro g w l
      obtain ⟨m, r, u, hu⟩ := hF.expo g w
      have e1 : ∀ t, T t g w = ∑ i, ((Real.exp (r i * t) : ℝ) : ℂ) • (⟨e (u i), idem_mem hsm hKc _⟩ : W) := by
        intro t
        apply Subtype.ext
        rw [hT, hu t, map_sum, Submodule.coe_sum]
        simp only [map_smul, Submodule.coe_smul]
      simp_rw [e1, map_sum, map_smul, smul_eq_mul]
      refine continuous_finset_sum _ fun i _ => Continuous.mul ?_ continuous_const
      exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hsimple : ∀ t, 0 ≤ t → ∀ U : Submodule ℂ W, (∀ g, ∀ w ∈ U, T t g w ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro t ht U hU
      by_cases hU0 : U = ⊥
      · exact Or.inl hU0
      right
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      let S : Submodule ℂ V := Submodule.span ℂ (Set.range fun g => F t g u)
      have hS : ∀ g, ∀ x ∈ S, F t g x ∈ S := by
        intro g x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨g', rfl⟩ := hy
          exact Submodule.subset_span ⟨g * g', by simp only [map_mul, Module.End.mul_apply]⟩
        | zero => simp
        | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
        | smul c x _ hx => rw [map_smul]; exact S.smul_mem c hx
      have hSt : S = ⊤ := by
        rcases irr_sub (hall t ht).2.2.1 S hS with h1 | h1
        · exfalso
          apply hu0
          apply Subtype.ext
          have : ((u : W) : V) ∈ S := Submodule.subset_span ⟨1, by simp⟩
          rw [h1, Submodule.mem_bot] at this
          simpa using this
        · exact h1
      have hmem : ∀ x ∈ S, (⟨e x, idem_mem hsm hKc x⟩ : W) ∈ U := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨g, rfl⟩ := hy
          exact hU g u huU
        | zero =>
          convert U.zero_mem using 1
          exact Subtype.ext (by simp)
        | add x y _ _ hx hy =>
          have : (⟨e (x + y), idem_mem hsm hKc _⟩ : W) = ⟨e x, idem_mem hsm hKc _⟩ + ⟨e y, idem_mem hsm hKc _⟩ :=
            Subtype.ext (by simp)
          rw [this]; exact U.add_mem hx hy
        | smul c x _ hx =>
          have : (⟨e (c • x), idem_mem hsm hKc _⟩ : W) = c • ⟨e x, idem_mem hsm hKc _⟩ := Subtype.ext (by simp)
          rw [this]; exact U.smul_mem c hx
      refine eq_top_iff.2 fun w _ => ?_
      have hw : (⟨e w, idem_mem hsm hKc _⟩ : W) = w := Subtype.ext (idem_of_mem hsm hKc w.2)
      rw [← hw]
      exact hmem w (hSt ▸ Submodule.mem_top)
    haveI : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).2 hW
    have hresne : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) →
        (F t).IsIrreducible → C ≠ 0 → resF C W ≠ 0 := by
      intro t C hCi hi hC0 h0'
      obtain ⟨w, hw0⟩ := exists_ne (0 : W)
      obtain ⟨x, hx⟩ := nondeg hi C hC0 hCi w (fun e0 => hw0 (Subtype.ext e0))
      apply hx
      rw [← (hleft t C hCi x w w.2).2]
      have := congrArg (fun f => f w ⟨e x, idem_mem hsm hKc x⟩) h0'
      simpa using this
    have hforms : ∀ t, 0 ≤ t → ∃ C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ, C ≠ 0 ∧
        (∀ v w, C w v = starRingEnd ℂ (C v w)) ∧ ∀ g v w, C (T t g v) w = C v (T t g⁻¹ w) := by
      intro t ht
      obtain ⟨C, hC0, hCh, hCi⟩ := exists_herm (hall t ht).2.2.2
      exact ⟨resF C W, hresne t C hCi (hall t ht).2.2.1 hC0, fun v w => hCh v w, hinvW t C hCi⟩
    have hpos0 : ∃ C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ, (∀ v w, C w v = starRingEnd ℂ (C v w)) ∧
        (∀ v, v ≠ 0 → 0 < (C v v).re) ∧ ∀ g v w, C (T 0 g v) w = C v (T 0 g⁻¹ w) :=
      ⟨resF B₀ W, fun v w => hB₀h v w, fun v hv => hB₀p v (fun e0 => hv (Subtype.ext e0)), hinvW 0 B₀ hB₀i⟩
    rcases h G W (fun g => g⁻¹) T (fun i w l => hcont i w l) hsimple hforms hpos0 inv_surjective s hs (resF H W)
        (hresne s H hHi hirr hH0) (fun v w => hHh v w) (hinvW s H hHi) with h1 | h1
    · exact Or.inl fun w hw hw0 => h1 ⟨w, hw⟩ (fun e0 => hw0 (congrArg Subtype.val e0))
    · exact Or.inr fun w hw hw0 => h1 ⟨w, hw⟩ (fun e0 => hw0 (congrArg Subtype.val e0))
  obtain ⟨v₁, hv₁⟩ := exists_ne (0 : V)
  have hopen : ∀ v : V, IsOpen ((stabG (F 0) v : Subgroup G) : Set G) := fun v => hsm v
  let K₁ : Subgroup G := K₀ ⊓ stabG (F 0) v₁
  have hK₁o : IsOpen (K₁ : Set G) := hK₀o.inter (hopen v₁)
  have hv₁K : ∀ K : Subgroup G, K ≤ K₁ → v₁ ∈ fixed (F 0) K :=
    fun K hK => GlobalTheory.Parabolic.mem_fixed.2 fun g hg => (hK hg).2
  have hne : ∀ K : Subgroup G, K ≤ K₁ → fixed (F 0) K ≠ ⊥ := fun K hK h' => by
    have := hv₁K K hK
    rw [h', Submodule.mem_bot] at this
    exact hv₁ this
  have hloc : ∀ v : V, v ≠ 0 → ((0 < (H v₁ v₁).re → 0 < (H v v).re) ∧ ((H v₁ v₁).re < 0 → (H v v).re < 0)) := by
    intro v hv
    let Kv : Subgroup G := K₁ ⊓ stabG (F 0) v
    have hKvo : IsOpen (Kv : Set G) := hK₁o.inter (hopen v)
    have hvK : v ∈ fixed (F 0) Kv := GlobalTheory.Parabolic.mem_fixed.2 fun g hg => hg.2
    rcases key Kv hKvo (inf_le_left.trans inf_le_left) (hne Kv inf_le_left) with h1 | h1
    · have a := h1 v hvK hv
      have b := h1 v₁ (hv₁K Kv inf_le_left) hv₁
      exact ⟨fun _ => a, fun hb => absurd b (not_lt.2 hb.le)⟩
    · have a := h1 v hvK hv
      have b := h1 v₁ (hv₁K Kv inf_le_left) hv₁
      exact ⟨fun hb => absurd b (not_lt.2 hb.le), fun _ => a⟩
  rcases key K₁ hK₁o inf_le_left (hne K₁ le_rfl) with h1 | h1
  · have hp := h1 v₁ (hv₁K K₁ le_rfl) hv₁
    exact ⟨H, fun v w => hHh v w, fun v hv => (hloc v hv).1 hp, hHi⟩
  · have hn := h1 v₁ (hv₁K K₁ le_rfl) hv₁
    refine ⟨-H, fun v w => ?_, fun v hv => ?_, fun g v w => ?_⟩
    · simp [hHh v w]
    · have := (hloc v hv).2 hn
      simp only [LinearMap.neg_apply, Complex.neg_re]
      linarith
    · simp [hHi]

end PositivityTheory.RgGu.NR
