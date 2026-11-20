import Mathlib

noncomputable def UpperTheory.Reformulated.B.Gwa5.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

/- English proof (translation)
Introduce `k G V _ _ _ _ ρ H χ a b ha hb h`. Rewrite using `[map_add, smul_add, ha h, hb h]`.
-/
theorem UpperTheory.Reformulated.B.Gwa5.aux2 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V},
      a ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        b ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
          ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (a + b) = (↑((χ : ↥H → kˣ) h) : k) • (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  rw [map_add, smul_add, ha h, hb h]

/- English proof (translation)
Introduce `k G V _ _ _ _ ρ H χ h`. Rewrite using `[map_zero, smul_zero]`.
-/
theorem UpperTheory.Reformulated.B.Gwa5.aux3 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H),
      ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (0 : V) = (↑((χ : ↥H → kˣ) h) : k) • (0 : V) := by
  intro k G V _ _ _ _ ρ H χ h
  rw [map_zero, smul_zero]

/- English proof (translation)
Introduce `k G V _ _ _ _ ρ H χ c v hv h`. Rewrite using `[map_smul, hv h, smul_comm]`.
-/
theorem UpperTheory.Reformulated.B.Gwa5.aux4 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V},
      v ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (c • v) = (↑((χ : ↥H → kˣ) h) : k) • c • v := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  rw [map_smul, hv h, smul_comm]

noncomputable def UpperTheory.Reformulated.B.Gwa5.eig :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
    fun {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
        (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦
      { carrier := {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v},
        add_mem' := @UpperTheory.Reformulated.B.Gwa5.aux2 k G V inst inst_1 inst_2 inst_3 ρ H χ, zero_mem' := UpperTheory.Reformulated.B.Gwa5.aux3 ρ H χ,
        smul_mem' := UpperTheory.Reformulated.B.Gwa5.aux4 ρ H χ : Submodule k V }

noncomputable def UpperTheory.Reformulated.B.Gwa5.fixed :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → Representation k G V → Subgroup G → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V)
        (H : Subgroup G) ↦
      UpperTheory.Reformulated.B.Gwa5.eig ρ H (1 : ↥H →* kˣ)

/- English proof (translation)
Introduce `G V _ _ _ _ _ J L A _ hJc π hπ q u _ hL hAJ hA hdec`. Establish `hmul : ∀ (x y : G) (w : V), π x (π y w) = π (x * y) w`. Introduce `x y w`. Rewrite using `[map_mul, Module.End.mul_apply]`. Establish `hq : ∀ y ∈ J, π y u - u ∈ q`.

Introduce `y hy`. Take `⟨a, ha, hl⟩` from `hdec y hy`. Establish `h1 : π y u = π a u` using `by conv_rhs => rw [← hL _ hl, hmul, mul_inv_cancel_left]`. Rewrite using `[h1]`. Conclude with `hA a ha`.

Establish `hfin : ((fun g : G => π g u) '' (J : Set G)).Finite`. Establish `hU : ∀ x ∈ (J : Set G), {g : G | π g u = π x u} ∈ nhds x`. Introduce `x _`. Establish `ho : IsOpen ((fun g : G => x⁻¹ * g) ⁻¹' {g : G | π g u = u})` using `(hπ u).preimage (continuous_const.mul continuous_id)`. Use `Filter.mem_of_superset (ho.mem_nhds ?_) ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Introduce `g hg`. Establish `hg' : π (x⁻¹ * g) u = u` using `hg`. Use `show π g u = π x u`. Use `conv_rhs => rw [← hg', hmul, mul_inv_cancel_left]`.

Take `⟨t, -, ht⟩` from `hJc.elim_nhds_subcover _ hU`. Use `(t.finite_toSet.image (fun g : G => π g u)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Take `⟨x, hx, hgx⟩` from `Set.mem_iUnion₂.1 (ht hg)`. Conclude with `⟨x, hx, hgx.symm⟩`.

Use `set O : Finset V := hfin.toFinset with hO`. Establish `hmem : ∀ w, w ∈ O ↔ ∃ g ∈ J, π g u = w`. Introduce `w`. Rewrite using `[hO, Set.Finite.mem_toFinset]`. Both sides reduce to the same expression.

Establish `hstab : ∀ h ∈ J, ∀ w ∈ O, π h w ∈ O`. Introduce `h hh w hw`. Take `⟨g, hg, rfl⟩` from `(hmem w).1 hw`. Conclude with `(hmem _).2 ⟨h * g, J.mul_mem hh hg, (hmul h g u).symm⟩`. Establish `hne : (O.card : ℂ) ≠ 0`.

Establish `: O.Nonempty` using `⟨π 1 u, (hmem _).2 ⟨1, J.one_mem, rfl⟩⟩`. Conclude with `this.card_pos.ne'` after adjusting the coercions. Use `⟨(O.card : ℂ)⁻¹ • ∑ w ∈ O, w, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `hs : ∑ w ∈ O, π (h : G) w = ∑ w ∈ O, w`.

Use `Finset.sum_nbij' (fun w => π (h : G) w) (fun w => π (h : G)⁻¹ w) (fun w hw => hstab _ h.2 w hw) (fun w hw => hstab _ (J.inv_mem h.2) w hw) ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `w _`. Simplify using `only [hmul, inv_mul_cancel, map_one, Module.End.one_apply]`. Introduce `w _`. Simplify using `only [hmul, mul_inv_cancel, map_one, Module.End.one_apply]`.

Rewrite using `[map_smul, map_sum, hs, MonoidHom.one_apply, Units.val_one, one_smul]`. Establish `h2 : (O.card : ℂ)⁻¹ • ∑ w ∈ O, w - u = (O.card : ℂ)⁻¹ • ∑ w ∈ O, (w - u)`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hne, one_smul]`. Rewrite using `[h2]`. Use `q.smul_mem _ (q.sum_mem ?_)` and prove the remaining obligations.

Introduce `w hw`. Take `⟨g, hg, rfl⟩` from `(hmem w).1 hw`. Conclude with `hq g hg`.
-/
theorem UpperTheory.Reformulated.B.Gwa5.exists_fixed_lift :
    ∀ {G V : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (J L A : Subgroup G),
      IsOpen (↑J : Set G) →
        IsCompact (↑J : Set G) →
          ∀ (π : Representation ℂ G V),
            UpperTheory.Reformulated.B.Gwa5.IsSmooth π →
              ∀ (q : Submodule ℂ V) (u : V),
                L ≤ J →
                  (∀ y ∈ L, ((π : G → V →ₗ[ℂ] V) y : V → V) u = u) →
                    A ≤ J →
                      (∀ x ∈ A, ((π : G → V →ₗ[ℂ] V) x : V → V) u - u ∈ q) →
                        (∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ L) → ∃ v ∈ UpperTheory.Reformulated.B.Gwa5.fixed π J, v - u ∈ q := by
  intro G V _ _ _ _ _ J L A _ hJc π hπ q u _ hL hAJ hA hdec
  classical
  have hmul : ∀ (x y : G) (w : V), π x (π y w) = π (x * y) w := by
    intro x y w
    rw [map_mul, Module.End.mul_apply]

  have hq : ∀ y ∈ J, π y u - u ∈ q := by
    intro y hy
    obtain ⟨a, ha, hl⟩ := hdec y hy
    have h1 : π y u = π a u := by
      conv_rhs => rw [← hL _ hl, hmul, mul_inv_cancel_left]
    rw [h1]
    exact hA a ha

  have hfin : ((fun g : G => π g u) '' (J : Set G)).Finite := by
    have hU : ∀ x ∈ (J : Set G), {g : G | π g u = π x u} ∈ nhds x := by
      intro x _
      have ho : IsOpen ((fun g : G => x⁻¹ * g) ⁻¹' {g : G | π g u = u}) :=
        (hπ u).preimage (continuous_const.mul continuous_id)
      refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
      · simp
      · intro g hg
        have hg' : π (x⁻¹ * g) u = u := hg
        show π g u = π x u
        conv_rhs => rw [← hg', hmul, mul_inv_cancel_left]
    obtain ⟨t, -, ht⟩ := hJc.elim_nhds_subcover _ hU
    refine (t.finite_toSet.image (fun g : G => π g u)).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, hx, hgx⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact ⟨x, hx, hgx.symm⟩
  set O : Finset V := hfin.toFinset with hO
  have hmem : ∀ w, w ∈ O ↔ ∃ g ∈ J, π g u = w := by
    intro w
    rw [hO, Set.Finite.mem_toFinset]
    rfl
  have hstab : ∀ h ∈ J, ∀ w ∈ O, π h w ∈ O := by
    intro h hh w hw
    obtain ⟨g, hg, rfl⟩ := (hmem w).1 hw
    exact (hmem _).2 ⟨h * g, J.mul_mem hh hg, (hmul h g u).symm⟩
  have hne : (O.card : ℂ) ≠ 0 := by
    have : O.Nonempty := ⟨π 1 u, (hmem _).2 ⟨1, J.one_mem, rfl⟩⟩
    exact_mod_cast this.card_pos.ne'
  refine ⟨(O.card : ℂ)⁻¹ • ∑ w ∈ O, w, ?_, ?_⟩
  · intro h
    have hs : ∑ w ∈ O, π (h : G) w = ∑ w ∈ O, w := by
      refine Finset.sum_nbij' (fun w => π (h : G) w) (fun w => π (h : G)⁻¹ w)
        (fun w hw => hstab _ h.2 w hw) (fun w hw => hstab _ (J.inv_mem h.2) w hw) ?_ ?_
        (fun _ _ => rfl)
      · intro w _
        simp only [hmul, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro w _
        simp only [hmul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_smul, map_sum, hs, MonoidHom.one_apply, Units.val_one, one_smul]
  · have h2 : (O.card : ℂ)⁻¹ • ∑ w ∈ O, w - u = (O.card : ℂ)⁻¹ • ∑ w ∈ O, (w - u) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ,
        smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [h2]
    refine q.smul_mem _ (q.sum_mem ?_)
    intro w hw
    obtain ⟨g, hg, rfl⟩ := (hmem w).1 hw
    exact hq g hg
