import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne

open Module GlobalTheory.HTRho

noncomputable section

namespace GlobalTheory.HTRho.FilDim

variable {k H O C : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨c, x, hx, rfl⟩`.
-/
theorem mSub_gen (σ : O →+* Module.End k H) (χ : C →+* k) {X : Submodule k H} (c : C) {x : H}
    (hx : x ∈ X) : σ (algebraMap C O c) x - χ c • x ∈ mSub σ χ X :=
  Submodule.subset_span ⟨c, x, hx, rfl⟩

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, x, hx, rfl⟩`. Conclude with `X.sub_mem (hX _ x hx) (X.smul_mem _ hx)`.
-/
theorem mSub_le_of_stable (σ : O →+* Module.End k H) (χ : C →+* k) (X : Submodule k H)
    (hX : ∀ a, ∀ x ∈ X, σ a x ∈ X) : mSub σ χ X ≤ X := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, x, hx, rfl⟩
  exact X.sub_mem (hX _ x hx) (X.smul_mem _ hx)

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, x, hx, rfl⟩`. Conclude with `⟨c, x, h hx, rfl⟩`.
-/
theorem mSub_mono (σ : O →+* Module.End k H) (χ : C →+* k) {X Y : Submodule k H} (h : X ≤ Y) :
    mSub σ χ X ≤ mSub σ χ Y := by
  refine Submodule.span_mono ?_
  rintro _ ⟨c, x, hx, rfl⟩
  exact ⟨c, x, h hx, rfl⟩

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨r, lam, c, x, hx, hc, rfl⟩`. Conclude with `⟨r, lam, c, x, h hx, hc, rfl⟩`.
-/
theorem jSub_mono {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) {X Y : Submodule k H}
    (h : X ≤ Y) : jSub σ χ X ≤ jSub σ χ Y := by
  refine Submodule.span_mono ?_
  rintro _ ⟨r, lam, c, x, hx, hc, rfl⟩
  exact ⟨r, lam, c, x, h hx, hc, rfl⟩

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨r, lam, c, x, hx, hc, rfl⟩`. Establish `e : ∑ l, lam l • σ (algebraMap C O (c l)) x = ∑ l, lam l • (σ (algebraMap C O (c l)) x - χ i (c l) • x) + (∑ l, lam l * χ i (c l)) • x`. Simplify using `only [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, smul_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e, hc i, zero_smul, add_zero]`. Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (mSub_gen σ (χ i) (c l) hx)`.
-/
theorem jSub_le_mSub {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) (X : Submodule k H)
    (i : ι) : jSub σ χ X ≤ mSub σ (χ i) X := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨r, lam, c, x, hx, hc, rfl⟩
  have e : ∑ l, lam l • σ (algebraMap C O (c l)) x
      = ∑ l, lam l • (σ (algebraMap C O (c l)) x - χ i (c l) • x) + (∑ l, lam l * χ i (c l)) • x := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, smul_smul]
    abel
  rw [e, hc i, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (mSub_gen σ (χ i) (c l) hx)

/- English proof (translation)
Set `e` to `Fintype.equivFin β`. Use `Submodule.subset_span ⟨Fintype.card β, lam ∘ e.symm, c ∘ e.symm, x, hx, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← h i]`. Conclude with `Fintype.sum_equiv e.symm _ _ (fun _ => rfl)`. Conclude with `(Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm`.
-/
theorem jSub_gen {ι β : Type*} [Fintype β] (σ : O →+* Module.End k H) (χ : ι → C →+* k)
    {X : Submodule k H} (lam : β → k) (c : β → C) {x : H} (hx : x ∈ X)
    (h : ∀ i, ∑ l, lam l * χ i (c l) = 0) :
    ∑ l, lam l • σ (algebraMap C O (c l)) x ∈ jSub σ χ X := by
  let e := Fintype.equivFin β
  refine Submodule.subset_span ⟨Fintype.card β, lam ∘ e.symm, c ∘ e.symm, x, hx, fun i => ?_, ?_⟩
  · rw [← h i]; exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  · exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm

/- English proof (translation)
Rewrite using `[mSub, Submodule.map_span, mSub]`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, ⟨c, x, _, rfl⟩, rfl⟩`.

Conclude with `⟨c, x, x.2, by simp⟩`. Introduce and unpack `⟨c, x, hx, rfl⟩`. Conclude with `⟨_, ⟨c, ⟨x, hx⟩, trivial, rfl⟩, by simp⟩`.
-/
theorem mSub_rAct (σ : O →+* Module.End k H) (χ : C →+* k) (G : Submodule k H)
    (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) :
    (mSub (rAct σ G hG) χ ⊤).map G.subtype = mSub σ χ G := by
  rw [mSub, Submodule.map_span, mSub]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨c, x, _, rfl⟩, rfl⟩
    exact ⟨c, x, x.2, by simp⟩
  · rintro ⟨c, x, hx, rfl⟩
    exact ⟨_, ⟨c, ⟨x, hx⟩, trivial, rfl⟩, by simp⟩

/- English proof (translation)
Simplify using `only [mSub]`. Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, q, _, rfl⟩`. Take `⟨x, rfl⟩` from `X.mkQ_surjective q`. Conclude with `⟨_, ⟨c, x, trivial, rfl⟩, by simp; rfl⟩`. Introduce and unpack `⟨w, ⟨c, x, _, rfl⟩, rfl⟩`. Conclude with `⟨c, X.mkQ x, trivial, by simp; rfl⟩`.
-/
theorem mSub_qAct {V : Type*} [AddCommGroup V] [Module k V] (τ : O →+* Module.End k V) (χ : C →+* k)
    (X : Submodule k V) (h : ∀ a, ∀ x ∈ X, τ a x ∈ X) :
    mSub (qAct τ X h) χ ⊤ = (mSub τ χ ⊤).map X.mkQ := by
  simp only [mSub]
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨c, q, _, rfl⟩
    obtain ⟨x, rfl⟩ := X.mkQ_surjective q
    exact ⟨_, ⟨c, x, trivial, rfl⟩, by simp; rfl⟩
  · rintro ⟨w, ⟨c, x, _, rfl⟩, rfl⟩
    exact ⟨c, X.mkQ x, trivial, by simp; rfl⟩

/- English proof (translation)
Set `v : C → (Idx → k)` to `fun d j => χ j d`. Establish `hmem : (Pi.single i 1 : Idx → k) ∈ Submodule.span k (Set.range v)`. Assume the negation of the conclusion as `hx`. Take `⟨f, hf, hf'⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance`. Establish `hli : LinearIndependent k (fun j => ((χ j : C →* k) : C → k))`.

Use `linearIndependent_monoidHom C k` as an intermediate fact. Use `this.comp (fun j => (χ j : C →* k)) ?_` and prove the remaining obligations. Introduce `a b hab`. Apply `hχ` to reduce the goal to its premises. Use extensionality with `c`.

Conclude with `DFunLike.congr_fun hab c`. Establish `hzero : ∑ j, f (Pi.single j 1) • ((χ j : C →* k) : C → k) = 0`. Use function extensionality and compare the values at `d`. Establish `h1 : f (v d) = 0`. Establish `: f (v d) ∈ (Submodule.span k (Set.range v)).map f` using `Submodule.mem_map_of_mem (Submodule.subset_span ⟨d, rfl⟩)`.

Rewrite `this` using `[hf']`. Conclude with `this`. Rewrite `h1` using `[LinearMap.pi_apply_eq_sum_univ f (v d)]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Rewrite using `[← h1]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [v, smul_eq_mul, MonoidHom.coe_coe]`. Rewrite using `[mul_comm]`. Use `congr 2`. Use function extensionality and compare the values at `j'`.

Simplify using `[Pi.single_apply, eq_comm]`. Establish `ha` using `Fintype.linearIndependent_iff.1 hli _ hzero`. Apply `hf` to reduce the goal to its premises. Rewrite using `[LinearMap.pi_apply_eq_sum_univ f (Pi.single i 1)]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Establish `hs : (fun j' => if j = j' then (1 : k) else 0) = Pi.single j 1`. Use function extensionality and compare the values at `j'`. Simplify using `[Pi.single_apply, eq_comm]`. Rewrite using `[hs, ha j, smul_zero]`. Take `⟨c, hc⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 hmem`.

Use `⟨c.support, c, fun j => ?_⟩` and prove the remaining obligations. Use `congrFun hc j` as an intermediate fact. Simplify using `only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v] at this`. Rewrite using `[this, Pi.single_apply]`.
-/
theorem exists_delta {Idx : Type*} [Fintype Idx] [DecidableEq Idx] (χ : Idx → C →+* k)
    (hχ : Function.Injective χ) (i : Idx) :
    ∃ S : Finset C, ∃ lam : C → k, ∀ j, ∑ d ∈ S, lam d * χ j d = if j = i then 1 else 0 := by
  let v : C → (Idx → k) := fun d j => χ j d
  have hmem : (Pi.single i 1 : Idx → k) ∈ Submodule.span k (Set.range v) := by
    by_contra hx
    obtain ⟨f, hf, hf'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hli : LinearIndependent k (fun j => ((χ j : C →* k) : C → k)) := by
      have := linearIndependent_monoidHom C k
      refine this.comp (fun j => (χ j : C →* k)) ?_
      intro a b hab
      apply hχ
      ext c
      exact DFunLike.congr_fun hab c
    have hzero : ∑ j, f (Pi.single j 1) • ((χ j : C →* k) : C → k) = 0 := by
      funext d
      have h1 : f (v d) = 0 := by
        have : f (v d) ∈ (Submodule.span k (Set.range v)).map f :=
          Submodule.mem_map_of_mem (Submodule.subset_span ⟨d, rfl⟩)
        rw [hf'] at this
        exact this
      rw [LinearMap.pi_apply_eq_sum_univ f (v d)] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [v, smul_eq_mul, MonoidHom.coe_coe]
      rw [mul_comm]
      congr 2
      funext j'
      simp [Pi.single_apply, eq_comm]
    have ha := Fintype.linearIndependent_iff.1 hli _ hzero
    apply hf
    rw [LinearMap.pi_apply_eq_sum_univ f (Pi.single i 1)]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hs : (fun j' => if j = j' then (1 : k) else 0) = Pi.single j 1 := by
      funext j'; simp [Pi.single_apply, eq_comm]
    rw [hs, ha j, smul_zero]
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨c.support, c, fun j => ?_⟩
  have := congrFun hc j
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v] at this
  rw [this, Pi.single_apply]

/- English proof (translation)
Rewrite using `[mSub, Submodule.map_span]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨c, z, _, rfl⟩, rfl⟩`. Use `Submodule.subset_span ⟨c, T z, ⟨z, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `[hT]`.
-/
theorem mSub_map_le (σ : O →+* Module.End k H) (χ : C →+* k) (T : Module.End k H)
    (hT : ∀ c z, T (σ (algebraMap C O c) z) = σ (algebraMap C O c) (T z)) :
    (mSub σ χ ⊤).map T ≤ mSub σ χ (LinearMap.range T) := by
  rw [mSub, Submodule.map_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨c, z, _, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨c, T z, ⟨z, rfl⟩, ?_⟩
  simp [hT]

/- English proof (translation)
Establish `hA : LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) ≤ mSub σ (χ i) G`. Introduce and unpack `y ⟨z, rfl⟩`. Establish `h0 : ((σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1)) z = 0`. Rewrite using `[hw]`. Both sides reduce to the same expression.

Establish `e1 : σ (algebraMap C O ω) ((σ (algebraMap C O ω) - r₀ • 1) z) - r₀ • (σ (algebraMap C O ω) - r₀ • 1) z = (r₁ - r₀) • (σ (algebraMap C O ω) - r₀ • 1) z`. Establish `: σ (algebraMap C O ω) ((σ (algebraMap C O ω) - r₀ • 1) z) - r₀ • (σ (algebraMap C O ω) - r₀ • 1) z = ((σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1)) z + (r₁ - r₀) • (σ (algebraMap C O ω) - r₀ • 1) z`. Simplify using `only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]`. Use `module`. Rewrite using `[this, h0, zero_add]`.

Establish `hg` using `mSub_gen σ (χ i) ω (hR ⟨z, rfl⟩)`. Rewrite `hg` using `[hχω i, e1]`. Establish `hne : r₁ - r₀ ≠ 0` using `sub_ne_zero.2 (Ne.symm hr)`. Use `Submodule.smul_mem _ (r₁ - r₀)⁻¹ hg` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hne, one_smul]`. Then use the resulting hypothesis.

Establish `hcomm : ∀ c z, (σ (algebraMap C O ω) - r₁ • 1) (σ (algebraMap C O c) z) = σ (algebraMap C O c) ((σ (algebraMap C O ω) - r₁ • 1) z)`. Introduce `c z`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]`. Use `congr 1`. Establish `: algebraMap C O ω * algebraMap C O c = algebraMap C O c * algebraMap C O ω`.

Rewrite using `[← map_mul, mul_comm, map_mul]`. Rewrite using `[← Module.End.mul_apply, ← map_mul σ, this, map_mul σ, Module.End.mul_apply]`. Introduce and unpack `x ⟨hxG, hxM⟩`. Establish `hx : x = (r₀ - r₁)⁻¹ • (σ (algebraMap C O ω) - r₁ • 1) x - (r₀ - r₁)⁻¹ • (σ (algebraMap C O ω) - r₀ • 1) x`. Establish `hne : r₀ - r₁ ≠ 0` using `sub_ne_zero.2 hr`.

Establish `: (σ (algebraMap C O ω) - r₁ • 1) x - (σ (algebraMap C O ω) - r₀ • 1) x = (r₀ - r₁) • x`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`. Use `module`. Rewrite using `[← smul_sub, this, smul_smul, inv_mul_cancel₀ hne, one_smul]`. Establish `hq : (σ (algebraMap C O ω) - r₀ • 1) x ∈ mSub σ (χ i) G` using `hA ⟨x, rfl⟩`.

Use `set p := (σ (algebraMap C O ω) - r₁ • 1) x with hp_def`. Establish `hpG : p ∈ G`. Rewrite using `[hp_def]`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`. Conclude with `G.sub_mem (hG _ x hxG) (G.smul_mem _ hxG)`.

Establish `hpR : p ∈ mSub σ (χ i) (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))` using `mSub_map_le σ (χ i) _ hcomm (Submodule.mem_map_of_mem hxM)`. Take `⟨S, lam, hδ⟩` from `exists_delta χ hχ i`. Set `E : Module.End k H` to `∑ d ∈ S, lam d • σ (algebraMap C O d)`. Establish `hEapp : ∀ v, E v = ∑ d ∈ S, lam d • σ (algebraMap C O d) v`. Introduce `v`.

Simplify using `[E, LinearMap.sum_apply]`. Establish `hE : ∀ v ∈ mSub σ (χ i) (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)), E v ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨c, y, hy, rfl⟩` from `hz`. Establish `key` using `jSub_gen σ χ (β := S ⊕ S) (Sum.elim (fun d => lam d) (fun d => -(lam d * χ i c))) (Sum.elim (fun d => (d : C) * c) (fun d => (d : C))) hy (by`. Introduce `j`. Rewrite using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, map_mul]`.

Rewrite using `[Finset.sum_coe_sort S (fun d => lam d * (χ j d * χ j c)), Finset.sum_coe_sort S (fun d => -(lam d * χ i c) * χ j d)]`. Establish `h1 : ∑ d ∈ S, lam d * (χ j d * χ j c) = (∑ d ∈ S, lam d * χ j d) * χ j c`. Rewrite using `[Finset.sum_mul]; exact Finset.sum_congr rfl fun d _ => by ring`. Establish `h2 : ∑ d ∈ S, -(lam d * χ i c) * χ j d = -(χ i c) * ∑ d ∈ S, lam d * χ j d`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring`.

Rewrite using `[h1, h2, hδ j]`. Use `split_ifs with h`. Substitute `h` using the available equality. Expand and normalize the polynomial expressions, which then agree. Use the proof step `ring)`.

Use `key using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hEapp, Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, map_mul, Module.End.mul_apply, neg_smul, Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_coe_sort S (fun d => lam d • σ (algebraMap C O d) (σ (algebraMap C O c) y)), Finset.sum_coe_sort S (fun d => (lam d * χ i c) • σ (algebraMap C O d) y)]`. Simplify using `only [map_sub, map_smul, smul_sub, Finset.sum_sub_distrib, smul_smul]`.

Rewrite using `[sub_eq_add_neg]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx => rw [map_smul]`.

Conclude with `Submodule.smul_mem _ a hx`. Establish `hpE : p - E p ∈ mSub σ (χ i) G`. Establish `: p - E p = -∑ d ∈ S, lam d • (σ (algebraMap C O d) p - χ i d • p)`. Rewrite using `[hEapp]`. Simplify using `only [smul_sub, Finset.sum_sub_distrib, smul_smul]`.

Rewrite using `[← Finset.sum_smul, hδ i, if_pos rfl, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `neg_mem (Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (mSub_gen σ (χ i) d hpG))`. Establish `hp : p ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) ⊔ mSub σ (χ i) G`.

Establish `: p = E p + (p - E p)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem_sup (hE p hpR) hpE`. Rewrite using `[hx]`. Conclude with `Submodule.sub_mem _ (Submodule.smul_mem _ _ hp) (Submodule.smul_mem _ _ (Submodule.mem_sup_right hq))`.
-/
theorem inf_le_sup {Idx : Type*} [Fintype Idx] (σ : O →+* Module.End k H) (χ : Idx → C →+* k)
    (hχ : Function.Injective χ) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (ω : C) (r₀ r₁ : k)
    (hr : r₀ ≠ r₁)
    (hw : (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0)
    (hχω : ∀ i, χ i ω = r₀) (hR : LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) ≤ G) (i : Idx) :
    G ⊓ mSub σ (χ i) ⊤ ≤
      jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) ⊔ mSub σ (χ i) G := by
  classical
  have hA : LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) ≤ mSub σ (χ i) G := by
    rintro y ⟨z, rfl⟩
    have h0 : ((σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1)) z = 0 := by
      rw [hw]; rfl
    have e1 : σ (algebraMap C O ω) ((σ (algebraMap C O ω) - r₀ • 1) z) - r₀ • (σ (algebraMap C O ω) - r₀ • 1) z
        = (r₁ - r₀) • (σ (algebraMap C O ω) - r₀ • 1) z := by
      have : σ (algebraMap C O ω) ((σ (algebraMap C O ω) - r₀ • 1) z) - r₀ • (σ (algebraMap C O ω) - r₀ • 1) z
          = ((σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1)) z
            + (r₁ - r₀) • (σ (algebraMap C O ω) - r₀ • 1) z := by
        simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          map_sub, map_smul]
        module
      rw [this, h0, zero_add]
    have hg := mSub_gen σ (χ i) ω (hR ⟨z, rfl⟩)
    rw [hχω i, e1] at hg
    have hne : r₁ - r₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hr)
    have := Submodule.smul_mem _ (r₁ - r₀)⁻¹ hg
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hcomm : ∀ c z, (σ (algebraMap C O ω) - r₁ • 1) (σ (algebraMap C O c) z)
      = σ (algebraMap C O c) ((σ (algebraMap C O ω) - r₁ • 1) z) := by
    intro c z
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
    congr 1
    have : algebraMap C O ω * algebraMap C O c = algebraMap C O c * algebraMap C O ω := by
      rw [← map_mul, mul_comm, map_mul]
    rw [← Module.End.mul_apply, ← map_mul σ, this, map_mul σ, Module.End.mul_apply]
  rintro x ⟨hxG, hxM⟩
  have hx : x = (r₀ - r₁)⁻¹ • (σ (algebraMap C O ω) - r₁ • 1) x
      - (r₀ - r₁)⁻¹ • (σ (algebraMap C O ω) - r₀ • 1) x := by
    have hne : r₀ - r₁ ≠ 0 := sub_ne_zero.2 hr
    have : (σ (algebraMap C O ω) - r₁ • 1) x - (σ (algebraMap C O ω) - r₀ • 1) x = (r₀ - r₁) • x := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      module
    rw [← smul_sub, this, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hq : (σ (algebraMap C O ω) - r₀ • 1) x ∈ mSub σ (χ i) G := hA ⟨x, rfl⟩
  set p := (σ (algebraMap C O ω) - r₁ • 1) x with hp_def
  have hpG : p ∈ G := by
    rw [hp_def]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact G.sub_mem (hG _ x hxG) (G.smul_mem _ hxG)
  have hpR : p ∈ mSub σ (χ i) (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) :=
    mSub_map_le σ (χ i) _ hcomm (Submodule.mem_map_of_mem hxM)
  obtain ⟨S, lam, hδ⟩ := exists_delta χ hχ i
  let E : Module.End k H := ∑ d ∈ S, lam d • σ (algebraMap C O d)
  have hEapp : ∀ v, E v = ∑ d ∈ S, lam d • σ (algebraMap C O d) v := by
    intro v; simp [E, LinearMap.sum_apply]
  have hE : ∀ v ∈ mSub σ (χ i) (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)),
      E v ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, y, hy, rfl⟩ := hz
      have key := jSub_gen σ χ (β := S ⊕ S)
        (Sum.elim (fun d => lam d) (fun d => -(lam d * χ i c)))
        (Sum.elim (fun d => (d : C) * c) (fun d => (d : C))) hy (by
          intro j
          rw [Fintype.sum_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr, map_mul]
          rw [Finset.sum_coe_sort S (fun d => lam d * (χ j d * χ j c)),
            Finset.sum_coe_sort S (fun d => -(lam d * χ i c) * χ j d)]
          have h1 : ∑ d ∈ S, lam d * (χ j d * χ j c) = (∑ d ∈ S, lam d * χ j d) * χ j c := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun d _ => by ring
          have h2 : ∑ d ∈ S, -(lam d * χ i c) * χ j d = -(χ i c) * ∑ d ∈ S, lam d * χ j d := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
          rw [h1, h2, hδ j]
          split_ifs with h
          · subst h; ring
          · ring)
      convert key using 1
      rw [hEapp, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, map_mul, Module.End.mul_apply, neg_smul, Finset.sum_neg_distrib]
      rw [Finset.sum_coe_sort S (fun d => lam d • σ (algebraMap C O d) (σ (algebraMap C O c) y)),
        Finset.sum_coe_sort S (fun d => (lam d * χ i c) • σ (algebraMap C O d) y)]
      simp only [map_sub, map_smul, smul_sub, Finset.sum_sub_distrib, smul_smul]
      rw [sub_eq_add_neg]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  have hpE : p - E p ∈ mSub σ (χ i) G := by
    have : p - E p = -∑ d ∈ S, lam d • (σ (algebraMap C O d) p - χ i d • p) := by
      rw [hEapp]
      simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
      rw [← Finset.sum_smul, hδ i, if_pos rfl, one_smul]
      abel
    rw [this]
    exact neg_mem (Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (mSub_gen σ (χ i) d hpG))
  have hp : p ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) ⊔ mSub σ (χ i) G := by
    have : p = E p + (p - E p) := by abel
    rw [this]
    exact Submodule.add_mem_sup (hE p hpR) hpE
  rw [hx]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hp)
    (Submodule.smul_mem _ _ (Submodule.mem_sup_right hq))

end GlobalTheory.HTRho.FilDim

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

/- English proof (translation)
Introduce `k O C Idx H _ _ _ _ _ _ _ _ σ χ hχ Fil hFil ω r₀ r₁ hr hw hχω hG hZ hJ i G Z σW`. Establish `hZG : Z ≤ G` using `(GlobalTheory.HTRho.FilDim.jSub_mono σ χ le_top).trans hJ`. Establish `hZM : Z ≤ mSub σ (χ i) ⊤` using `(GlobalTheory.HTRho.FilDim.jSub_le_mSub σ χ _ i).trans (GlobalTheory.HTRho.FilDim.mSub_mono σ (χ i) le_top)`. Establish `hmG : mSub σ (χ i) G ≤ G ⊓ mSub σ (χ i) ⊤` using `le_inf (GlobalTheory.HTRho.FilDim.mSub_le_of_stable σ _ G hG) (GlobalTheory.HTRho.FilDim.mSub_mono _ _ le_top)`. Establish `heq : Z ⊔ mSub σ (χ i) G = G ⊓ mSub σ (χ i) ⊤` using `le_antisymm (sup_le (le_inf hZG hZM) hmG) (GlobalTheory.HTRho.FilDim.inf_le_sup σ χ hχ G hG ω r₀ r₁ hr hw hχω le_sup_right i)`.

Set `N : Submodule k G` to `mSub (rAct σ G hG) (χ i) ⊤ ⊔ Z.comap G.subtype`. Establish `hσW : mSub σW (χ i) ⊤ = N.map (Z.comap G.subtype).mkQ`. Use `(GlobalTheory.HTRho.FilDim.mSub_qAct (rAct σ G hG) (χ i) (Z.comap G.subtype) _).trans ?_` and prove the remaining obligations. Simplify using `only [N]`. Rewrite using `[Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]`.

Establish `e1 : finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) = finrank k (G ⧸ N)`. Rewrite using `[hσW]`. Conclude with `(Submodule.quotientQuotientEquivQuotient (Z.comap G.subtype) N le_sup_right).finrank_eq`. Establish `hNmap : N.map G.subtype = G ⊓ mSub σ (χ i) ⊤`. Simplify using `only [N]`.

Rewrite using `[Submodule.map_sup, GlobalTheory.HTRho.FilDim.mSub_rAct, Submodule.map_comap_subtype, inf_eq_right.2 hZG, sup_comm, heq]`. Establish `e2 : finrank k N = finrank k ↥(G ⊓ mSub σ (χ i) ⊤)`. Use `(Submodule.equivMapOfInjective G.subtype G.injective_subtype N).finrank_eq` as an intermediate fact. Rewrite `this` using `[hNmap]`. Conclude with `this`.

Establish `a1` using `Submodule.finrank_quotient_add_finrank N`. Establish `a2` using `Submodule.finrank_quotient_add_finrank (G ⊔ mSub σ (χ i) ⊤)`. Establish `a3` using `Submodule.finrank_quotient_add_finrank (mSub σ (χ i) ⊤)`. Establish `a4` using `Submodule.finrank_sup_add_finrank_inf_eq G (mSub σ (χ i) ⊤)`. Rewrite using `[e1]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem GlobalTheory.HTRho.FilDim.finrank_fildim : ∀ {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O] [Fintype Idx] [FiniteDimensional k H] (σ : O →+* Module.End k H) (χ : Idx → C →+* k), Function.Injective χ → ∀ (Fil : Submodule k H), (∀ a, ∀ x ∈ Fil, σ a x ∈ Fil) → ∀ (ω : C) (r₀ r₁ : k), r₀ ≠ r₁ → (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0 → (∀ i, χ i ω = r₀) → ∀ (hG : ∀ a, ∀ x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1), σ a x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) (hZ : ∀ a, ∀ x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)), σ a x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))), jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) → ∀ (i : Idx), let G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1); let Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)); let σW := qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx); finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) + finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) = finrank k (H ⧸ mSub σ (χ i) ⊤) := by
  intro k O C Idx H _ _ _ _ _ _ _ _ σ χ hχ Fil hFil ω r₀ r₁ hr hw hχω hG hZ hJ i G Z σW
  classical
  have hZG : Z ≤ G := (GlobalTheory.HTRho.FilDim.jSub_mono σ χ le_top).trans hJ
  have hZM : Z ≤ mSub σ (χ i) ⊤ :=
    (GlobalTheory.HTRho.FilDim.jSub_le_mSub σ χ _ i).trans (GlobalTheory.HTRho.FilDim.mSub_mono σ (χ i) le_top)
  have hmG : mSub σ (χ i) G ≤ G ⊓ mSub σ (χ i) ⊤ :=
    le_inf (GlobalTheory.HTRho.FilDim.mSub_le_of_stable σ _ G hG) (GlobalTheory.HTRho.FilDim.mSub_mono _ _ le_top)
  have heq : Z ⊔ mSub σ (χ i) G = G ⊓ mSub σ (χ i) ⊤ :=
    le_antisymm (sup_le (le_inf hZG hZM) hmG)
      (GlobalTheory.HTRho.FilDim.inf_le_sup σ χ hχ G hG ω r₀ r₁ hr hw hχω le_sup_right i)
  let N : Submodule k G := mSub (rAct σ G hG) (χ i) ⊤ ⊔ Z.comap G.subtype
  have hσW : mSub σW (χ i) ⊤ = N.map (Z.comap G.subtype).mkQ := by
    refine (GlobalTheory.HTRho.FilDim.mSub_qAct (rAct σ G hG) (χ i) (Z.comap G.subtype) _).trans ?_
    simp only [N]
    rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  have e1 : finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) = finrank k (G ⧸ N) := by
    rw [hσW]
    exact (Submodule.quotientQuotientEquivQuotient (Z.comap G.subtype) N le_sup_right).finrank_eq
  have hNmap : N.map G.subtype = G ⊓ mSub σ (χ i) ⊤ := by
    simp only [N]
    rw [Submodule.map_sup, GlobalTheory.HTRho.FilDim.mSub_rAct, Submodule.map_comap_subtype,
      inf_eq_right.2 hZG, sup_comm, heq]
  have e2 : finrank k N = finrank k ↥(G ⊓ mSub σ (χ i) ⊤) := by
    have := (Submodule.equivMapOfInjective G.subtype G.injective_subtype N).finrank_eq
    rw [hNmap] at this
    exact this
  have a1 := Submodule.finrank_quotient_add_finrank N
  have a2 := Submodule.finrank_quotient_add_finrank (G ⊔ mSub σ (χ i) ⊤)
  have a3 := Submodule.finrank_quotient_add_finrank (mSub σ (χ i) ⊤)
  have a4 := Submodule.finrank_sup_add_finrank_inf_eq G (mSub σ (χ i) ⊤)
  rw [e1]
  omega
