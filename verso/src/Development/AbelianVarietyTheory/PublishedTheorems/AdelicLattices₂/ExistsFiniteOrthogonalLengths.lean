import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsIntMulIsIntegralOfTrace

namespace GlobalTheory.HermClass

open Module Submodule NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_bound_short (E := E) n hn hN`. Take `⟨M, hM, hMJ⟩` from `exists_int_mul_mem_span E`. Set `L : Submodule ℤ E` to `Subalgebra.toSubmodule (integralClosure ℤ E) ⊓ LinearMap.ker ((starRingEnd E).toIntAlgHom.toLinearMap - LinearMap.id)`. Establish `hL : ∀ x, x ∈ L ↔ IsIntegral ℤ x ∧ star x = x` using `fun x => by`. Simplify using `[L, sub_eq_zero, mem_integralClosure_iff, starRingEnd_apply]`.

Establish `hLfg : L.FG` using `(fg_integers E).of_le inf_le_left`. Establish `hK : 2 * (N * M) ≠ 0` using `by positivity`. Take `⟨R, hR, -, hRL⟩` from `exists_finite_residues L hLfg hK`. Use `⟨({x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C} ∪ R ∪ {((2 * (N * M) : ℤ) : E)}) \ {0}, (((Embeddings.finite_of_norm_le E ℂ C).union hR).union (Set.finite_singleton _)).subset Set.diff_subset, by simp, ?_⟩` and prove the remaining obligations. Introduce `V _ _ _ h Λ hV hs hnd hfg hsp hO hint hdual`.

Take `⟨v, hv, hv0, hvC⟩` from `hC V h Λ hV hs hfg hsp hO hdual`. Distinguish the cases in `hvv : h v v = 0`. Use `swap`. Conclude with `⟨v, hv, Or.inl (Or.inl ⟨hint v hv v hv, hvC⟩), hvv⟩`. Set `J : Ideal (𝓞 E)` to `{ carrier := {a | ∃ x ∈ Λ, h x v = algebraMap (𝓞 E) E a} add_mem' := by`.

Introduce and unpack `a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩`. Conclude with `⟨x + y, add_mem hx hy, by simp [ha, hb]⟩`. Use the proof step `zero_mem' := ⟨0, zero_mem _, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨x, hx, ha⟩`.

Conclude with `⟨algebraMap (𝓞 E) E c • x, hO _ c.isIntegral_coe x hx, by`. Rewrite using `[map_smul, LinearMap.smul_apply, ha, smul_eq_mul, smul_eq_mul, map_mul]⟩ }`. Establish `hJ : ∀ x ∈ Λ, ∃ a ∈ J, algebraMap (𝓞 E) E a = h x v` using `fun x hx => ⟨⟨h x v, hint x hx v hv⟩, ⟨x, hx, rfl⟩, rfl⟩`. Establish `hJ0 : J ≠ ⊥`. Introduce `h0`.

Use `hv0 (hnd v fun x => ?_)` and prove the remaining obligations. Establish `h1 : span E (Λ : Set V) ≤ LinearMap.ker (h.flip v)` using `span_le.2 fun y hy => by`. Take `⟨a, ha, hay⟩` from `hJ y hy`. Rewrite `ha` using `[h0, Ideal.mem_bot]`. Rewrite `hay` using `[ha, map_zero]`.

Conclude with `hay.symm`. Establish `h2 : h x v = 0` using `h1 (hsp ▸ mem_top)`. Rewrite using `[hs, h2, star_zero]`. Take `⟨j, ⟨w, hw, hwj⟩, hj0, hj⟩` from `hMJ J hJ0`. Establish `hj0' : algebraMap (𝓞 E) E j ≠ 0` using `fun h0 => hj0 (RingOfIntegers.ext h0)`.

Use `set v' : V := (N : E) • star ((M : E) / algebraMap (𝓞 E) E j) • v with hv'`. Establish `hv'Λ : v' ∈ Λ` using `hdual _ fun x hx => by`. Take `⟨a, ha, hax⟩` from `hJ x hx`. Take `⟨c, hc⟩` from `hj _ ha`. Establish `hc'` using `congrArg (algebraMap (𝓞 E) E) hc`.

Rewrite `hc'` using `[map_mul, map_mul, map_intCast, hax]`. Establish `: (M : E) / algebraMap (𝓞 E) E j * h x v = algebraMap (𝓞 E) E c` using `by field_simp; exact hc'`. Rewrite using `[map_smul, LinearMap.smul_apply, smul_eq_mul, hs x v, ← star_mul', this]`. Conclude with `isIntegral_star c.isIntegral_coe`. Establish `h1 : h w v' = N * M`.

Simplify using `only [hv', map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, hwj, star_intCast]`. Clear the denominators using the available nonvanishing facts. Establish `h2 : h v' w = N * M` using `by rw [hs, h1]; simp`. Establish `h3 : h v' v' = 0` using `by simp [hv', hvv]`. Establish `h4 : ∀ s : E, star s = s → h (w - s • v') (w - s • v') = h w w - 2 * (N * M) * s`.

Introduce `s hs'`. Simplify using `only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_smulₛₗ, starRingEnd_apply, hs', smul_eq_mul, h1, h2, h3, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨ρ, hρ, y, hy, hwρ⟩` from `hRL (h w w) ((hL _).2 ⟨hint w hw w hw, (hs w w).symm⟩)`. Take `⟨hyi, hys⟩` from `(hL y).1 hy`.

Distinguish the cases in `hρ0 : ρ = 0`. Use `⟨w - (y - 1) • v', sub_mem hw (hO _ (hyi.sub isIntegral_one) _ hv'Λ), ?_⟩` and prove the remaining obligations. Establish `: h (w - (y - 1) • v') (w - (y - 1) • v') = ((2 * (N * M) : ℤ) : E)`. Rewrite using `[h4 _ (by rw [star_sub, hys, star_one]), hwρ, hρ0, zsmul_eq_mul]; push_cast; ring`. Rewrite using `[this]`.

Conclude with `⟨Or.inr rfl, by simpa using hK⟩`. Use `⟨w - y • v', sub_mem hw (hO _ hyi _ hv'Λ), ?_⟩` and prove the remaining obligations. Establish `: h (w - y • v') (w - y • v') = ρ`. Rewrite using `[h4 _ hys, hwρ, zsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `⟨Or.inl (Or.inr hρ), hρ0⟩`.
-/
theorem exists_finite_lengths (n : ℕ) (hn : n ≠ 0) {N : ℤ} (hN : N ≠ 0) :
    ∃ S : Set E, S.Finite ∧ (0 : E) ∉ S ∧
      ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V), finrank E V = n →
      (∀ x y, h y x = star (h x y)) → (∀ y, (∀ x, h y x = 0) → y = 0) →
      Λ.FG → span E (Λ : Set V) = ⊤ →
      (∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (h x y)) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ) →
      ∃ v ∈ Λ, h v v ∈ S := by
  classical
  obtain ⟨C, hC⟩ := exists_bound_short (E := E) n hn hN
  obtain ⟨M, hM, hMJ⟩ := exists_int_mul_mem_span E
  let L : Submodule ℤ E := Subalgebra.toSubmodule (integralClosure ℤ E) ⊓
    LinearMap.ker ((starRingEnd E).toIntAlgHom.toLinearMap - LinearMap.id)
  have hL : ∀ x, x ∈ L ↔ IsIntegral ℤ x ∧ star x = x := fun x => by
    simp [L, sub_eq_zero, mem_integralClosure_iff, starRingEnd_apply]
  have hLfg : L.FG := (fg_integers E).of_le inf_le_left
  have hK : 2 * (N * M) ≠ 0 := by positivity
  obtain ⟨R, hR, -, hRL⟩ := exists_finite_residues L hLfg hK
  refine ⟨({x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C} ∪ R ∪
    {((2 * (N * M) : ℤ) : E)}) \ {0},
    (((Embeddings.finite_of_norm_le E ℂ C).union hR).union (Set.finite_singleton _)).subset
      Set.diff_subset, by simp, ?_⟩
  intro V _ _ _ h Λ hV hs hnd hfg hsp hO hint hdual
  obtain ⟨v, hv, hv0, hvC⟩ := hC V h Λ hV hs hfg hsp hO hdual
  by_cases hvv : h v v = 0
  swap
  · exact ⟨v, hv, Or.inl (Or.inl ⟨hint v hv v hv, hvC⟩), hvv⟩
  let J : Ideal (𝓞 E) :=
    { carrier := {a | ∃ x ∈ Λ, h x v = algebraMap (𝓞 E) E a}
      add_mem' := by
        rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
        exact ⟨x + y, add_mem hx hy, by simp [ha, hb]⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c a ⟨x, hx, ha⟩
        exact ⟨algebraMap (𝓞 E) E c • x, hO _ c.isIntegral_coe x hx, by
          rw [map_smul, LinearMap.smul_apply, ha, smul_eq_mul, smul_eq_mul, map_mul]⟩ }
  have hJ : ∀ x ∈ Λ, ∃ a ∈ J, algebraMap (𝓞 E) E a = h x v := fun x hx =>
    ⟨⟨h x v, hint x hx v hv⟩, ⟨x, hx, rfl⟩, rfl⟩
  have hJ0 : J ≠ ⊥ := by
    intro h0
    refine hv0 (hnd v fun x => ?_)
    have h1 : span E (Λ : Set V) ≤ LinearMap.ker (h.flip v) := span_le.2 fun y hy => by
      obtain ⟨a, ha, hay⟩ := hJ y hy
      rw [h0, Ideal.mem_bot] at ha
      rw [ha, map_zero] at hay
      exact hay.symm
    have h2 : h x v = 0 := h1 (hsp ▸ mem_top)
    rw [hs, h2, star_zero]
  obtain ⟨j, ⟨w, hw, hwj⟩, hj0, hj⟩ := hMJ J hJ0
  have hj0' : algebraMap (𝓞 E) E j ≠ 0 := fun h0 => hj0 (RingOfIntegers.ext h0)
  set v' : V := (N : E) • star ((M : E) / algebraMap (𝓞 E) E j) • v with hv'
  have hv'Λ : v' ∈ Λ := hdual _ fun x hx => by
    obtain ⟨a, ha, hax⟩ := hJ x hx
    obtain ⟨c, hc⟩ := hj _ ha
    have hc' := congrArg (algebraMap (𝓞 E) E) hc
    rw [map_mul, map_mul, map_intCast, hax] at hc'
    have : (M : E) / algebraMap (𝓞 E) E j * h x v = algebraMap (𝓞 E) E c := by
      field_simp; exact hc'
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hs x v, ← star_mul', this]
    exact isIntegral_star c.isIntegral_coe
  have h1 : h w v' = N * M := by
    simp only [hv', map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, hwj, star_intCast]
    field_simp
  have h2 : h v' w = N * M := by rw [hs, h1]; simp
  have h3 : h v' v' = 0 := by simp [hv', hvv]
  have h4 : ∀ s : E, star s = s → h (w - s • v') (w - s • v') = h w w - 2 * (N * M) * s := by
    intro s hs'
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, map_smulₛₗ,
      starRingEnd_apply, hs', smul_eq_mul, h1, h2, h3, RingHom.id_apply]
    ring
  obtain ⟨ρ, hρ, y, hy, hwρ⟩ := hRL (h w w) ((hL _).2 ⟨hint w hw w hw, (hs w w).symm⟩)
  obtain ⟨hyi, hys⟩ := (hL y).1 hy
  by_cases hρ0 : ρ = 0
  · refine ⟨w - (y - 1) • v', sub_mem hw (hO _ (hyi.sub isIntegral_one) _ hv'Λ), ?_⟩
    have : h (w - (y - 1) • v') (w - (y - 1) • v') = ((2 * (N * M) : ℤ) : E) := by
      rw [h4 _ (by rw [star_sub, hys, star_one]), hwρ, hρ0, zsmul_eq_mul]; push_cast; ring
    rw [this]
    exact ⟨Or.inr rfl, by simpa using hK⟩
  · refine ⟨w - y • v', sub_mem hw (hO _ hyi _ hv'Λ), ?_⟩
    have : h (w - y • v') (w - y • v') = ρ := by
      rw [h4 _ hys, hwρ, zsmul_eq_mul]; push_cast; ring
    rw [this]
    exact ⟨Or.inl (Or.inr hρ), hρ0⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `N _`. Conclude with `⟨∅, Set.finite_empty, by simp, fun V _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩`. Consider the case `succ n ih`.

Introduce `N hN`. Take `⟨S₁, hS₁, h0₁, H₁⟩` from `exists_finite_lengths (E := E) (n + 1) n.succ_ne_zero hN`. Take `⟨M, hM, hMS⟩` from `exists_int_mul_isIntegral E (hS₁.image fun a => a⁻¹)`. Take `⟨S₂, hS₂, h0₂, H₂⟩` from `ih (mul_ne_zero hM hN)`. Use `⟨S₁ ∪ S₂, hS₁.union hS₂, by simp [h0₁, h0₂], ?_⟩` and prove the remaining obligations.

Introduce `V _ _ _ h Λ hV hs hnd hfg hsp hO hint hdual`. Take `⟨v, hv, hvS⟩` from `H₁ V h Λ hV hs hnd hfg hsp hO hint hdual`. Use `set a := h v v with ha`. Establish `ha0 : a ≠ 0` using `fun h0 => h0₁ (h0 ▸ hvS)`. Establish `hai : IsIntegral ℤ a` using `hint v hv v hv`.

Establish `has : star a = a` using `(hs v v).symm`. Set `W : Submodule E V` to `LinearMap.ker (h.flip v)`. Establish `hW : ∀ x, x ∈ W ↔ h x v = 0` using `fun x => Iff.rfl`. Establish `hWr : finrank E W = n`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (h.flip v)`.

Establish `h2 : LinearMap.range (h.flip v) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `c _`. Conclude with `⟨(c / a) • v, by simp [← ha, ha0]⟩`. Rewrite `h1` using `[h2, finrank_top, finrank_self, hV]`.

Express the relevant statement in the definitionally equal form `1 + finrank E W = _ at h1`. Use linear arithmetic over natural numbers and integers. Set `p : V →ₗ[E] W` to `LinearMap.codRestrict W (a • LinearMap.id - (h.flip v).smulRight v) fun x => by`. Rewrite using `[hW]`. Simplify using `[← ha, mul_comm]`.

Establish `hp : ∀ x, (p x : V) = a • x - h x v • v` using `fun x => rfl`. Set `Λ' : Submodule ℤ W` to `Λ.comap (W.subtype.restrictScalars ℤ)`. Establish `hΛ' : ∀ x : W, x ∈ Λ' ↔ (x : V) ∈ Λ` using `fun x => Iff.rfl`. Establish `hpΛ : ∀ x ∈ Λ, p x ∈ Λ'` using `fun x hx => by`. Rewrite using `[hΛ', hp]`.

Conclude with `sub_mem (hO _ hai _ hx) (hO _ (hint x hx v hv) _ hv)`. Establish `hyp : ∀ (y : W) (x : V), h y (p x) = a * h y x` using `fun y x => by`. Establish `: h y v = 0` using `y.2`. Simplify using `[hp, starRingEnd_apply, has, this]`. Take `⟨u, huΛ, huo, huS⟩` from `H₂ W (h.domRestrict₁₂ W W) Λ' hWr (fun x y => hs x y) (fun y hy => Subtype.ext (hnd y fun x => by`.

Establish `h1 : h y (p x) = 0` using `hy (p x)`. Rewrite `h1` using `[hyp]`. Conclude with `(mul_eq_zero.1 h1).resolve_left ha0))`. Use the proof step `(by`. Apply `Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars ℤ) W.subtype_injective` to reduce the goal to its premises.

Conclude with `hfg.of_le (map_comap_le _ _))`. Use the proof step `(by`. Rewrite using `[eq_top_iff]`. Introduce `w _`. Establish `h1 : span E (Λ : Set V) ≤ (span E (Λ' : Set W)).comap p` using `span_le.2 fun x hx => subset_span (hpΛ x hx)`.

Establish `h2 : p w ∈ span E (Λ' : Set W)` using `h1 (hsp ▸ mem_top)`. Establish `h3 : w = a⁻¹ • p w` using `Subtype.ext (by`. Establish `: h w v = 0` using `w.2`. Simplify using `[hp, this, ha0])`. Rewrite using `[h3]`.

Conclude with `smul_mem _ _ h2)`. Use the proof step `(fun c hc x hx => hO c hc x hx) (fun x hx y hy => hint x hx y hy)`. Use the proof step `(fun y hy => by`. Establish `h1 : (N : E) • a • (y : V) ∈ Λ` using `hdual _ fun x hx => by`. Rewrite using `[map_smul, LinearMap.smul_apply, smul_eq_mul, ← hyp]`.

Conclude with `hy _ (hpΛ x hx)`. Establish `h2` using `hO _ (hMS _ ⟨a, hvS, rfl⟩) _ h1`. Rewrite `h2` using `[smul_smul, smul_smul]`. Rewrite using `[hΛ', Submodule.coe_smul]`. Use `h2 using 2` and compare the differences between its conclusion and the goal.

Use `push_cast`. Use the proof step `field_simp)`. Use `⟨Fin.cons v fun i => u i, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Consider the cases of `i using Fin.cases with`. Consider the case `zero => exact hv`.

Consider the case `succ i => exact huΛ i`. Consider the cases of `i using Fin.cases with`. Consider the case `zero`. Consider the cases of `j using Fin.cases with`. Consider the case `zero => exact (hij rfl).elim`.

Consider the case `succ j`. Establish `: h (u j) v = 0` using `(u j).2`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[hs, this, star_zero]`. Consider the case `succ i`.

Consider the cases of `j using Fin.cases with`. Consider the case `zero => exact (u i).2`. Consider the case `succ j => exact huo i j fun h0 => hij (congrArg _ h0)`. Consider the cases of `i using Fin.cases with`. Consider the case `zero => exact Or.inl hvS`.

Consider the case `succ i => exact Or.inr (huS i)`.
-/
theorem exists_finite_orthogonal_lengths (n : ℕ) : ∀ {N : ℤ}, N ≠ 0 →
    ∃ S : Set E, S.Finite ∧ (0 : E) ∉ S ∧
      ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : V →ₗ[E] V →ₗ⋆[E] E) (Λ : Submodule ℤ V), finrank E V = n →
      (∀ x y, h y x = star (h x y)) → (∀ y, (∀ x, h y x = 0) → y = 0) →
      Λ.FG → span E (Λ : Set V) = ⊤ →
      (∀ a : E, IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (h x y)) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ (h y x)) → (N : E) • y ∈ Λ) →
      ∃ v : Fin n → V, (∀ i, v i ∈ Λ) ∧ (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
        ∀ i, h (v i) (v i) ∈ S := by
  induction n with
  | zero =>
    intro N _
    exact ⟨∅, Set.finite_empty, by simp, fun V _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro N hN
    obtain ⟨S₁, hS₁, h0₁, H₁⟩ := exists_finite_lengths (E := E) (n + 1) n.succ_ne_zero hN
    obtain ⟨M, hM, hMS⟩ := exists_int_mul_isIntegral E (hS₁.image fun a => a⁻¹)
    obtain ⟨S₂, hS₂, h0₂, H₂⟩ := ih (mul_ne_zero hM hN)
    refine ⟨S₁ ∪ S₂, hS₁.union hS₂, by simp [h0₁, h0₂], ?_⟩
    intro V _ _ _ h Λ hV hs hnd hfg hsp hO hint hdual
    obtain ⟨v, hv, hvS⟩ := H₁ V h Λ hV hs hnd hfg hsp hO hint hdual
    set a := h v v with ha
    have ha0 : a ≠ 0 := fun h0 => h0₁ (h0 ▸ hvS)
    have hai : IsIntegral ℤ a := hint v hv v hv
    have has : star a = a := (hs v v).symm
    let W : Submodule E V := LinearMap.ker (h.flip v)
    have hW : ∀ x, x ∈ W ↔ h x v = 0 := fun x => Iff.rfl
    have hWr : finrank E W = n := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (h.flip v)
      have h2 : LinearMap.range (h.flip v) = ⊤ := by
        rw [eq_top_iff]
        intro c _
        exact ⟨(c / a) • v, by simp [← ha, ha0]⟩
      rw [h2, finrank_top, finrank_self, hV] at h1
      change 1 + finrank E W = _ at h1
      omega
    let p : V →ₗ[E] W := LinearMap.codRestrict W
      (a • LinearMap.id - (h.flip v).smulRight v) fun x => by
        rw [hW]; simp [← ha, mul_comm]
    have hp : ∀ x, (p x : V) = a • x - h x v • v := fun x => rfl
    let Λ' : Submodule ℤ W := Λ.comap (W.subtype.restrictScalars ℤ)
    have hΛ' : ∀ x : W, x ∈ Λ' ↔ (x : V) ∈ Λ := fun x => Iff.rfl
    have hpΛ : ∀ x ∈ Λ, p x ∈ Λ' := fun x hx => by
      rw [hΛ', hp]; exact sub_mem (hO _ hai _ hx) (hO _ (hint x hx v hv) _ hv)
    have hyp : ∀ (y : W) (x : V), h y (p x) = a * h y x := fun y x => by
      have : h y v = 0 := y.2
      simp [hp, starRingEnd_apply, has, this]
    obtain ⟨u, huΛ, huo, huS⟩ := H₂ W (h.domRestrict₁₂ W W) Λ' hWr (fun x y => hs x y)
      (fun y hy => Subtype.ext (hnd y fun x => by
        have h1 : h y (p x) = 0 := hy (p x)
        rw [hyp] at h1
        exact (mul_eq_zero.1 h1).resolve_left ha0))
      (by
        apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars ℤ) W.subtype_injective
        exact hfg.of_le (map_comap_le _ _))
      (by
        rw [eq_top_iff]
        intro w _
        have h1 : span E (Λ : Set V) ≤ (span E (Λ' : Set W)).comap p :=
          span_le.2 fun x hx => subset_span (hpΛ x hx)
        have h2 : p w ∈ span E (Λ' : Set W) := h1 (hsp ▸ mem_top)
        have h3 : w = a⁻¹ • p w := Subtype.ext (by
          have : h w v = 0 := w.2
          simp [hp, this, ha0])
        rw [h3]; exact smul_mem _ _ h2)
      (fun c hc x hx => hO c hc x hx) (fun x hx y hy => hint x hx y hy)
      (fun y hy => by
        have h1 : (N : E) • a • (y : V) ∈ Λ := hdual _ fun x hx => by
          rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← hyp]
          exact hy _ (hpΛ x hx)
        have h2 := hO _ (hMS _ ⟨a, hvS, rfl⟩) _ h1
        rw [smul_smul, smul_smul] at h2
        rw [hΛ', Submodule.coe_smul]
        convert h2 using 2
        push_cast; field_simp)
    refine ⟨Fin.cons v fun i => u i, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · cases i using Fin.cases with
      | zero => exact hv
      | succ i => exact huΛ i
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
          have : h (u j) v = 0 := (u j).2
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hs, this, star_zero]
      | succ i =>
        cases j using Fin.cases with
        | zero => exact (u i).2
        | succ j => exact huo i j fun h0 => hij (congrArg _ h0)
    · cases i using Fin.cases with
      | zero => exact Or.inl hvS
      | succ i => exact Or.inr (huS i)

end GlobalTheory.HermClass
