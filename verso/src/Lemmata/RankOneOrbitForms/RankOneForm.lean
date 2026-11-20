import Mathlib

open Module NumberField

namespace Bl.RankOneOrbitForms

variable {K : Type} [Field K] {G : Type} [Group G] {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]

/- English proof (translation)
Take `⟨v, hv, hw⟩` from `finrank_eq_one_iff'.mp h1`. Use `choose a ha using fun x => hw ⟨f x, LinearMap.mem_range_self f x⟩`. Establish `hv' : (v : T) ≠ 0` using `fun h => hv (Subtype.ext h)`. Establish `hav : ∀ x, a x • (v : T) = f x` using `fun x => congrArg Subtype.val (ha x)`. Establish `inj` using `smul_left_injective K hv'`.

Set `φ : T →ₗ[K] K` to `{ toFun := a map_add' := fun x y => inj (by simp only [add_smul, hav, map_add]) map_smul' := fun c x => inj (by`. Simplify using `only [smul_eq_mul, mul_smul, hav, map_smul, RingHom.id_apply]) }`. Use `⟨φ, v, hv', ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Take `⟨y, hy⟩` from `LinearMap.mem_range.mp v.2`.

Apply `hv'` to reduce the goal to its premises. Rewrite using `[← hy, ← hav y]`. Establish `: a y = 0` using `LinearMap.congr_fun h0 y`. Rewrite using `[this, zero_smul]`. Use extensionality with `x`.

Simplify using `only [LinearMap.smulRight_apply]`. Conclude with `(hav x).symm`.
-/
private lemma rank_one_form (f : T →ₗ[K] T) (h1 : finrank K (LinearMap.range f) = 1) :
    ∃ (φ : T →ₗ[K] K) (v : T), v ≠ 0 ∧ φ ≠ 0 ∧ f = φ.smulRight v := by
  obtain ⟨v, hv, hw⟩ := finrank_eq_one_iff'.mp h1
  choose a ha using fun x => hw ⟨f x, LinearMap.mem_range_self f x⟩
  have hv' : (v : T) ≠ 0 := fun h => hv (Subtype.ext h)
  have hav : ∀ x, a x • (v : T) = f x := fun x => congrArg Subtype.val (ha x)
  have inj := smul_left_injective K hv'
  let φ : T →ₗ[K] K :=
    { toFun := a
      map_add' := fun x y => inj (by simp only [add_smul, hav, map_add])
      map_smul' := fun c x => inj (by
        simp only [smul_eq_mul, mul_smul, hav, map_smul, RingHom.id_apply]) }
  refine ⟨φ, v, hv', ?_, ?_⟩
  · intro h0
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp v.2
    apply hv'
    rw [← hy, ← hav y]
    have : a y = 0 := LinearMap.congr_fun h0 y
    rw [this, zero_smul]
  · ext x
    simp only [LinearMap.smulRight_apply]
    exact (hav x).symm

/- English proof (translation)
Establish `hinvar : ∀ g : G, ∀ w ∈ Submodule.span K (Set.range fun g => τ g v), τ g w ∈ Submodule.span K (Set.range fun g => τ g v)`. Introduce `g w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨h, rfl⟩` from `hx`.

Conclude with `Submodule.subset_span ⟨g * h, by show τ (g * h) v = τ g (τ h v); rw [map_mul]; rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`. Break down `hirr _ hinvar with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hv` to reduce the goal to its premises.

Establish `: τ 1 v ∈ Submodule.span K (Set.range fun g => τ g v)` using `Submodule.subset_span ⟨1, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot, map_one, Module.End.one_apply]`. Conclude with `this`. Conclude with `h`.
-/
private lemma span_orbit (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (v : T) (hv : v ≠ 0) : Submodule.span K (Set.range fun g => τ g v) = ⊤ := by
  have hinvar : ∀ g : G, ∀ w ∈ Submodule.span K (Set.range fun g => τ g v),
      τ g w ∈ Submodule.span K (Set.range fun g => τ g v) := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by show τ (g * h) v = τ g (τ h v); rw [map_mul]; rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  rcases hirr _ hinvar with h | h
  · exfalso
    apply hv
    have : τ 1 v ∈ Submodule.span K (Set.range fun g => τ g v) := Submodule.subset_span ⟨1, rfl⟩
    rw [h, Submodule.mem_bot, map_one, Module.End.one_apply] at this
    exact this
  · exact h

/- English proof (translation)
Set `W : Submodule K T` to `⨅ g : G, LinearMap.ker (φ ∘ₗ τ g)`. Establish `memW : ∀ y, y ∈ W ↔ ∀ g, φ (τ g y) = 0`. Introduce `y`. Simplify using `[W, Submodule.mem_iInf]`. Establish `hinvar : ∀ g : G, ∀ w ∈ W, τ g w ∈ W`.

Introduce `g w hw`. Rewrite `hw`, the goal using `[memW]`. Introduce `h`. Use `hw (h * g)` as an intermediate fact. Rewrite `this` using `[map_mul, Module.End.mul_apply]`. Then use the resulting hypothesis.

Break down `hirr W hinvar with h | h` into its components or cases. Establish `: x ∈ W` using `(memW x).2 hx`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `this`. It suffices to derive a contradiction.

Apply `hφ` to reduce the goal to its premises. Use extensionality with `y`. Establish `hy : y ∈ W` using `h ▸ Submodule.mem_top`. Use `(memW y).1 hy 1` as an intermediate fact. Simplify using `using this`.
-/
private lemma orbit_ker (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (φ : T →ₗ[K] K) (hφ : φ ≠ 0) (x : T) (hx : ∀ g, φ (τ g x) = 0) : x = 0 := by
  let W : Submodule K T := ⨅ g : G, LinearMap.ker (φ ∘ₗ τ g)
  have memW : ∀ y, y ∈ W ↔ ∀ g, φ (τ g y) = 0 := by
    intro y
    simp [W, Submodule.mem_iInf]
  have hinvar : ∀ g : G, ∀ w ∈ W, τ g w ∈ W := by
    intro g w hw
    rw [memW] at hw ⊢
    intro h
    have := hw (h * g)
    rwa [map_mul, Module.End.mul_apply] at this
  rcases hirr W hinvar with h | h
  · have : x ∈ W := (memW x).2 hx
    rw [h, Submodule.mem_bot] at this
    exact this
  · exfalso
    apply hφ
    ext y
    have hy : y ∈ W := h ▸ Submodule.mem_top
    have := (memW y).1 hy 1
    simpa using this

/- English proof (translation)
Take `⟨κ, a, -, hsp, hli⟩` from `exists_linearIndependent' K f`. Establish `: Finite κ` using `hli.finite`. Set `_ : Fintype κ` to `Fintype.ofFinite κ`. Establish `hc : Fintype.card κ = r`. Rewrite using `[← finrank_span_eq_card hli, hsp, hr]`.

Set `e : Fin r ≃ κ` to `(Fintype.equivFinOfCardEq hc).symm`. Conclude with `⟨a ∘ e, hli.comp e e.injective⟩`.
-/
private lemma select {ι M : Type} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (f : ι → M) (r : ℕ) (hr : finrank K (Submodule.span K (Set.range f)) = r) :
    ∃ s : Fin r → ι, LinearIndependent K (f ∘ s) := by
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K f
  have : Finite κ := hli.finite
  let _ : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ = r := by
    rw [← finrank_span_eq_card hli, hsp, hr]
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hc).symm
  exact ⟨a ∘ e, hli.comp e e.injective⟩

/- English proof (translation)
Take `⟨φ, v, hv, hφ, rfl⟩` from `rank_one_form ε₀ h1`. Establish `hspanT` using `span_orbit τ hirr v hv`. Establish `hspanR : Submodule.span K (Set.range fun g => ε (τ g v)) = LinearMap.range ε`. Establish `: (Set.range fun g => ε (τ g v)) = ε '' (Set.range fun g => τ g v)`. Use extensionality with `y`.

Simplify using the standard rewrite rules. Rewrite using `[this, ← Submodule.map_span, hspanT, Submodule.map_top]`. Take `⟨γ, hγ⟩` from `select (fun g => ε (τ g v)) (finrank K (LinearMap.range ε)) (by rw [hspanR])`. Establish `hle : Submodule.span K (Set.range ((fun g => ε (τ g v)) ∘ γ)) ≤ LinearMap.range ε`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `LinearMap.mem_range_self _ _`. Establish `hueq : Submodule.span K (Set.range ((fun g => ε (τ g v)) ∘ γ)) = LinearMap.range ε` using `Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_eq_card hγ, Fintype.card_fin])`. Set `w : G → Fin (finrank K (LinearMap.range ε)) → K` to `fun g j => φ (τ g (ε (τ (γ j) v)))`. Establish `hw : Submodule.span K (Set.range w) = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨ℓ, hℓ, hle'⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)`. Apply `hℓ` to reduce the goal to its premises. Set `b : Fin (finrank K (LinearMap.range ε)) → K` to `fun j => ℓ (fun k => if j = k then 1 else 0)`. Establish `key : ∀ g, ∑ j, w g j • b j = 0`.

Introduce `g`. Use `hle' (Submodule.subset_span ⟨g, rfl⟩)` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ]`. Conclude with `this`. Establish `hx : ∑ j, b j • ε (τ (γ j) v) = 0`.

Apply `orbit_ker τ hirr φ hφ` to reduce the goal to its premises. Introduce `g`. Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Use `key g` as an intermediate fact. Simplify using `only [w, smul_eq_mul] at this`.

Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `hz` using `Fintype.linearIndependent_iff.mp hγ b hx`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.pi_apply_eq_sum_univ, LinearMap.zero_apply]`.

Conclude with `Finset.sum_eq_zero fun j _ => by`. Establish `: ℓ (fun k => if j = k then 1 else 0) = 0` using `hz j`. Rewrite using `[this, smul_zero]`. Take `⟨δ, hδ⟩` from `select w (finrank K (LinearMap.range ε)) (by rw [hw, finrank_top, Module.finrank_fin_fun])`. Set `c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K` to `Matrix.of fun i j => φ (τ (δ i) (ε (τ (γ j) v)))`.

Establish `hc : IsUnit c` using `Matrix.linearIndependent_rows_iff_isUnit.mp hδ`. Establish `hcd : IsUnit c.det` using `(Matrix.isUnit_iff_isUnit_det c).mp hc`. Use `⟨γ, δ, c, hcd.ne_zero, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Rewrite using `[show (φ.smulRight v) ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j) = (φ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j)).smulRight v from LinearMap.ext fun _ => rfl, LinearMap.trace_smulRight]`.

Both sides reduce to the same expression. Introduce `i j`. Use extensionality with `x`. Simplify using `[c, smul_smul, mul_comm]`. Use extensionality with `x`.

Establish `hx : ε x ∈ Submodule.span K (Set.range ((fun g => ε (τ g v)) ∘ γ))` using `by rw [hueq]; exact LinearMap.mem_range_self ε x`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun K).mp hx`. Simplify using `only [Function.comp_apply] at ha`. Establish `hcoef : ∀ i, φ (τ (δ i) (ε x)) = ∑ k, c i k * a k`. Introduce `i`.

Rewrite using `[← ha]`. Simplify using `[c, map_sum, map_smul, mul_comm]`. Establish `hinv : ∀ j, ∑ i, c⁻¹ j i * ∑ k, c i k * a k = a j`. Introduce `j`. Use `congrFun (show Matrix.mulVec c⁻¹ (Matrix.mulVec c a) = a by` as an intermediate fact.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul c hcd, Matrix.one_mulVec]) j`. Simplify `this` using `[Matrix.mulVec, dotProduct]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.smulRight_apply, map_smul, hcoef]`. Rewrite using `[← ha]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← hinv j, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`.
-/
theorem goal1 (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ε₀ ε : T →ₗ[K] T) (h1 : finrank K (LinearMap.range ε₀) = 1) :
    ∃ (γ δ : Fin (finrank K (LinearMap.range ε)) → G)
      (c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K),
      c.det ≠ 0 ∧
      (∀ i j, c i j = LinearMap.trace K T (ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j))) ∧
      (∀ i j, ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j) ∘ₗ ε₀ = c i j • ε₀) ∧
      ∑ j, ∑ i, c⁻¹ j i • (ε ∘ₗ τ (γ j) ∘ₗ ε₀ ∘ₗ τ (δ i) ∘ₗ ε) = ε := by
  obtain ⟨φ, v, hv, hφ, rfl⟩ := rank_one_form ε₀ h1
  have hspanT := span_orbit τ hirr v hv
  have hspanR : Submodule.span K (Set.range fun g => ε (τ g v)) = LinearMap.range ε := by
    have : (Set.range fun g => ε (τ g v)) = ε '' (Set.range fun g => τ g v) := by
      ext y; simp
    rw [this, ← Submodule.map_span, hspanT, Submodule.map_top]
  obtain ⟨γ, hγ⟩ := select (fun g => ε (τ g v)) (finrank K (LinearMap.range ε)) (by rw [hspanR])
  have hle : Submodule.span K (Set.range ((fun g => ε (τ g v)) ∘ γ)) ≤ LinearMap.range ε := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact LinearMap.mem_range_self _ _
  have hueq : Submodule.span K (Set.range ((fun g => ε (τ g v)) ∘ γ)) = LinearMap.range ε :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_eq_card hγ, Fintype.card_fin])
  let w : G → Fin (finrank K (LinearMap.range ε)) → K := fun g j => φ (τ g (ε (τ (γ j) v)))
  have hw : Submodule.span K (Set.range w) = ⊤ := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hle'⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    apply hℓ
    let b : Fin (finrank K (LinearMap.range ε)) → K := fun j => ℓ (fun k => if j = k then 1 else 0)
    have key : ∀ g, ∑ j, w g j • b j = 0 := by
      intro g
      have := hle' (Submodule.subset_span ⟨g, rfl⟩)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at this
      exact this
    have hx : ∑ j, b j • ε (τ (γ j) v) = 0 := by
      apply orbit_ker τ hirr φ hφ
      intro g
      simp only [map_sum, map_smul, smul_eq_mul]
      have := key g
      simp only [w, smul_eq_mul] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hz := Fintype.linearIndependent_iff.mp hγ b hx
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.pi_apply_eq_sum_univ, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun j _ => by
      have : ℓ (fun k => if j = k then 1 else 0) = 0 := hz j
      rw [this, smul_zero]
  obtain ⟨δ, hδ⟩ := select w (finrank K (LinearMap.range ε))
    (by rw [hw, finrank_top, Module.finrank_fin_fun])
  let c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K :=
    Matrix.of fun i j => φ (τ (δ i) (ε (τ (γ j) v)))
  have hc : IsUnit c := Matrix.linearIndependent_rows_iff_isUnit.mp hδ
  have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).mp hc
  refine ⟨γ, δ, c, hcd.ne_zero, ?_, ?_, ?_⟩
  · intro i j
    rw [show (φ.smulRight v) ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j)
        = (φ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j)).smulRight v from LinearMap.ext fun _ => rfl,
      LinearMap.trace_smulRight]
    rfl
  · intro i j
    ext x
    simp [c, smul_smul, mul_comm]
  · ext x
    have hx : ε x ∈ Submodule.span K (Set.range ((fun g => ε (τ g v)) ∘ γ)) :=
      by rw [hueq]; exact LinearMap.mem_range_self ε x
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    simp only [Function.comp_apply] at ha
    have hcoef : ∀ i, φ (τ (δ i) (ε x)) = ∑ k, c i k * a k := by
      intro i
      rw [← ha]
      simp [c, map_sum, map_smul, mul_comm]
    have hinv : ∀ j, ∑ i, c⁻¹ j i * ∑ k, c i k * a k = a j := by
      intro j
      have := congrFun (show Matrix.mulVec c⁻¹ (Matrix.mulVec c a) = a by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul c hcd, Matrix.one_mulVec]) j
      simpa [Matrix.mulVec, dotProduct] using this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.smulRight_apply, map_smul, hcoef]
    rw [← ha]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hinv j, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]

end Bl.RankOneOrbitForms
