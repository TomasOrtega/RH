import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorRepApply

open GlobalTheory.JR GlobalTheory.JR.WeilProd Filter Topology

namespace GlobalTheory.JR.WeilProd.TensorTest

section Basic
variable {X : Type} [TopologicalSpace X]

/- English proof (translation)
Use `⟨hg, ?_⟩` and prove the remaining obligations. Establish `hcl : IsClosed (Function.support g)` using `by show IsClosed {x | g x ≠ 0}`. Conclude with `(hg.isOpen_fiber 0).isClosed_compl`. Unfold `HasCompactSupport tsupport`. Rewrite using `[hcl.closure_eq]`.

Conclude with `hK.of_isClosed_subset hcl hs`.
-/
theorem isTest_of_lc {g : X → ℂ} (hg : IsLocallyConstant g) {K : Set X} (hK : IsCompact K)
    (hs : Function.support g ⊆ K) : IsTest g := by
  refine ⟨hg, ?_⟩
  have hcl : IsClosed (Function.support g) := by
    show IsClosed {x | g x ≠ 0}
    exact (hg.isOpen_fiber 0).isClosed_compl
  unfold HasCompactSupport tsupport
  rw [hcl.closure_eq]
  exact hK.of_isClosed_subset hcl hs

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩`.
-/
theorem isTest_zero : IsTest (0 : X → ℂ) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.1.add hf'.1, hf.2.add hf'.2⟩`.
-/
theorem isTest_add {f f' : X → ℂ} (hf : IsTest f) (hf' : IsTest f') : IsTest (f + f') :=
  ⟨hf.1.add hf'.1, hf.2.add hf'.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.1.comp (c * ·), hf.2.smul_left⟩`.
-/
theorem isTest_smul (c : ℂ) {f : X → ℂ} (hf : IsTest f) : IsTest (c • f) :=
  ⟨hf.1.comp (c * ·), hf.2.smul_left⟩

/- English proof (translation)
Use `revert hF`. Use `Finset.induction_on s (fun _ => by simpa using (isTest_zero : IsTest (0 : X → ℂ))) ?_` and prove the remaining obligations. Introduce `a s ha ih hF`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `isTest_add (hF a (Finset.mem_insert_self a s)) (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))`.
-/
theorem isTest_sum {ι : Type} (s : Finset ι) (F : ι → X → ℂ) (hF : ∀ j ∈ s, IsTest (F j)) :
    IsTest (∑ j ∈ s, F j) := by
  classical
  revert hF
  refine Finset.induction_on s (fun _ => by simpa using (isTest_zero : IsTest (0 : X → ℂ))) ?_
  intro a s ha ih hF
  rw [Finset.sum_insert ha]
  exact isTest_add (hF a (Finset.mem_insert_self a s)) (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Use `hW.2.2.2 g 1 0 0 isTest_zero isTest_zero` as an intermediate fact. Simplify using `using this`.
-/
theorem map_zero {G : Type} [Group G] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W) (g : G) : W g 0 = 0 := by
  have := hW.2.2.2 g 1 0 0 isTest_zero isTest_zero
  simpa using this

/- English proof (translation)
Use `revert hf`. Use `Finset.induction_on s (fun _ => by simp [map_zero hW g]) ?_` and prove the remaining obligations. Introduce `a s ha ih hf`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Establish `hs : IsTest (∑ j ∈ s, c j • f j)` using `isTest_sum s _ fun j hj => isTest_smul _ (hf j (Finset.mem_insert_of_mem hj))`.

Rewrite using `[hW.2.2.2 g (c a) (f a) _ (hf a (Finset.mem_insert_self a s)) hs, ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]`.
-/
theorem map_sum {G : Type} [Group G] {W : G → (X → ℂ) → X → ℂ} (hW : IsTestRep W) (g : G) {ι : Type}
    (s : Finset ι) (c : ι → ℂ) (f : ι → X → ℂ) (hf : ∀ j ∈ s, IsTest (f j)) :
    W g (∑ j ∈ s, c j • f j) = ∑ j ∈ s, c j • W g (f j) := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => by simp [map_zero hW g]) ?_
  intro a s ha ih hf
  rw [Finset.sum_insert ha, Finset.sum_insert ha]
  have hs : IsTest (∑ j ∈ s, c j • f j) :=
    isTest_sum s _ fun j hj => isTest_smul _ (hf j (Finset.mem_insert_of_mem hj))
  rw [hW.2.2.2 g (c a) (f a) _ (hf a (Finset.mem_insert_self a s)) hs,
    ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

end Basic

section Prod
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/- English proof (translation)
Use `isTest_of_lc ?_ (ha.2.isCompact.prod hb.2.isCompact) ?_` and prove the remaining obligations. Conclude with `IsLocallyConstant.comp₂ (ha.1.comp_continuous continuous_fst) (hb.1.comp_continuous continuous_snd) (fun x y => x * y)`. Introduce `p hp`. Establish `h1 : a p.1 ≠ 0` using `left_ne_zero_of_mul hp`. Establish `h2 : b p.2 ≠ 0` using `right_ne_zero_of_mul hp`.

Conclude with `⟨subset_tsupport _ h1, subset_tsupport _ h2⟩`.
-/
theorem isTest_mul_prod {a : X → ℂ} {b : Y → ℂ} (ha : IsTest a) (hb : IsTest b) :
    IsTest (fun p : X × Y => a p.1 * b p.2) := by
  refine isTest_of_lc ?_ (ha.2.isCompact.prod hb.2.isCompact) ?_
  · exact IsLocallyConstant.comp₂ (ha.1.comp_continuous continuous_fst) (hb.1.comp_continuous continuous_snd)
      (fun x y => x * y)
  · intro p hp
    have h1 : a p.1 ≠ 0 := left_ne_zero_of_mul hp
    have h2 : b p.2 ≠ 0 := right_ne_zero_of_mul hp
    exact ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩

/- English proof (translation)
Use `isTest_of_lc (hf.1.comp_continuous (continuous_const.prodMk continuous_id)) (hf.2.isCompact.image continuous_snd) ?_` and prove the remaining obligations. Introduce `v hv`. Conclude with `⟨(u, v), subset_tsupport _ hv, rfl⟩`.
-/
theorem isTest_fibre {f : X × Y → ℂ} (hf : IsTest f) (u : X) : IsTest (fun v => f (u, v)) := by
  refine isTest_of_lc (hf.1.comp_continuous (continuous_const.prodMk continuous_id)) (hf.2.isCompact.image continuous_snd) ?_
  intro v hv
  exact ⟨(u, v), subset_tsupport _ hv, rfl⟩

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `u₀`. Establish `hK : IsCompact (Prod.snd '' tsupport f)` using `hf.2.isCompact.image continuous_snd`. Establish `hev : ∀ᶠ u in 𝓝 u₀, ∀ v ∈ Prod.snd '' tsupport f, f (u, v) = f (u₀, v)`. Use `hK.eventually_forall_of_forall_eventually ?_` and prove the remaining obligations.

Introduce `y _`. Establish `h1 : ∀ᶠ z in 𝓝 (u₀, y), f z = f (u₀, y)` using `((IsLocallyConstant.iff_eventually_eq f).1 hf.1) (u₀, y)`. Establish `hc : Continuous (fun z : X × Y => (u₀, z.2))` using `(continuous_const.prodMk continuous_id).comp continuous_snd`. Establish `ht : Tendsto (fun z : X × Y => (u₀, z.2)) (𝓝 (u₀, y)) (𝓝 (u₀, y))` using `hc.continuousAt`. Establish `h2 : ∀ᶠ z in 𝓝 (u₀, y), f (u₀, z.2) = f (u₀, y)` using `ht.eventually (((IsLocallyConstant.iff_eventually_eq f).1 hf.1) (u₀, y))`.

Use `filter_upwards [h1, h2] with z hz1 hz2`. Rewrite using `[hz1, hz2]`. Use `filter_upwards [hev] with u hu`. Use function extensionality and compare the values at `v`. Distinguish the cases in `hv : v ∈ Prod.snd '' tsupport f`.

Conclude with `hu v hv`. Establish `hA : (u, v) ∉ tsupport f` using `fun h => hv ⟨_, h, rfl⟩`. Establish `hB : (u₀, v) ∉ tsupport f` using `fun h => hv ⟨_, h, rfl⟩`. Rewrite using `[image_eq_zero_of_notMem_tsupport hA, image_eq_zero_of_notMem_tsupport hB]`.
-/
theorem isLocallyConstant_curry {f : X × Y → ℂ} (hf : IsTest f) :
    IsLocallyConstant (fun u => fun v => f (u, v)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u₀
  have hK : IsCompact (Prod.snd '' tsupport f) := hf.2.isCompact.image continuous_snd
  have hev : ∀ᶠ u in 𝓝 u₀, ∀ v ∈ Prod.snd '' tsupport f, f (u, v) = f (u₀, v) := by
    refine hK.eventually_forall_of_forall_eventually ?_
    intro y _
    have h1 : ∀ᶠ z in 𝓝 (u₀, y), f z = f (u₀, y) := ((IsLocallyConstant.iff_eventually_eq f).1 hf.1) (u₀, y)
    have hc : Continuous (fun z : X × Y => (u₀, z.2)) := (continuous_const.prodMk continuous_id).comp continuous_snd
    have ht : Tendsto (fun z : X × Y => (u₀, z.2)) (𝓝 (u₀, y)) (𝓝 (u₀, y)) := hc.continuousAt
    have h2 : ∀ᶠ z in 𝓝 (u₀, y), f (u₀, z.2) = f (u₀, y) :=
      ht.eventually (((IsLocallyConstant.iff_eventually_eq f).1 hf.1) (u₀, y))
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2]
  filter_upwards [hev] with u hu
  funext v
  by_cases hv : v ∈ Prod.snd '' tsupport f
  · exact hu v hv
  · have hA : (u, v) ∉ tsupport f := fun h => hv ⟨_, h, rfl⟩
    have hB : (u₀, v) ∉ tsupport f := fun h => hv ⟨_, h, rfl⟩
    rw [image_eq_zero_of_notMem_tsupport hA, image_eq_zero_of_notMem_tsupport hB]

/- English proof (translation)
Use `isTest_sum s F hF` as an intermediate fact. Rewrite `this` using `[Finset.sum_fn]`. Then use the resulting hypothesis.
-/
theorem isTest_sum_fn {ι : Type} (s : Finset ι) (F : ι → X × Y → ℂ) (hF : ∀ j ∈ s, IsTest (F j)) :
    IsTest (fun p => ∑ j ∈ s, F j p) := by
  have := isTest_sum s F hF
  rwa [Finset.sum_fn] at this

/- English proof (translation)
Establish `hF : IsLocallyConstant (fun u => fun v => f (u, v))` using `isLocallyConstant_curry hf`. Establish `hK₁ : IsCompact (Prod.fst '' tsupport f)` using `hf.2.isCompact.image continuous_fst`. Establish `hzero : ∀ u, u ∉ Prod.fst '' tsupport f → (fun v => f (u, v)) = 0`. Introduce `u hu`. Use function extensionality and compare the values at `v`.

Assume the negation of the conclusion as `h`. Conclude with `hu ⟨(u, v), subset_tsupport _ h, rfl⟩`. Establish `hfin : (Set.range (fun u => fun v => f (u, v))).Finite`. Establish `: CompactSpace (Prod.fst '' tsupport f)` using `isCompact_iff_compactSpace.1 hK₁`. Establish `h1 : (Set.range ((fun u => fun v => f (u, v)) ∘ ((↑) : Prod.fst '' tsupport f → X))).Finite` using `(hF.comp_continuous continuous_subtype_val).range_finite`.

Use `(h1.union (Set.finite_singleton 0)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, rfl⟩`. Distinguish the cases in `hu : u ∈ Prod.fst '' tsupport f`. Conclude with `Or.inl ⟨⟨u, hu⟩, rfl⟩`. Conclude with `Or.inr (hzero u hu)`.

Use `⟨hfin.toFinset.erase 0, fun φ u => if (fun v => f (u, v)) = φ then 1 else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `φ hφ`. Establish `hφ0 : φ ≠ 0` using `Finset.ne_of_mem_erase hφ`. Use `isTest_of_lc (hF.comp fun ψ => if ψ = φ then (1:ℂ) else 0) hK₁ ?_` and prove the remaining obligations. Introduce `u hu`.

Assume the negation of the conclusion as `hK`. Apply `hu` to reduce the goal to its premises. Use `show (if (fun v => f (u, v)) = φ then (1:ℂ) else 0) = 0`. Rewrite using `[hzero u hK, if_neg (Ne.symm hφ0)]`. Introduce `φ hφ`.

Take `⟨u, rfl⟩ : φ ∈ Set.range (fun u => fun v => f (u, v))` from `(hfin.mem_toFinset).1 (Finset.mem_of_mem_erase hφ)`. Conclude with `isTest_fibre hf u`. Introduce and unpack `⟨u, v⟩`. Simplify using `only [ite_mul, one_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq]`.

Use `split_ifs with h`. Both sides reduce to the same expression. Establish `h0 : (fun v => f (u, v)) = 0`. Assume the negation of the conclusion as `h0`. Conclude with `h (Finset.mem_erase.2 ⟨h0, hfin.mem_toFinset.2 ⟨u, rfl⟩⟩)`.

Conclude with `congrFun h0 v`.
-/
theorem decomp {f : X × Y → ℂ} (hf : IsTest f) :
    ∃ (s : Finset (Y → ℂ)) (a : (Y → ℂ) → X → ℂ), (∀ φ ∈ s, IsTest (a φ)) ∧ (∀ φ ∈ s, IsTest φ) ∧
      ∀ p : X × Y, f p = ∑ φ ∈ s, a φ p.1 * φ p.2 := by
  classical
  have hF : IsLocallyConstant (fun u => fun v => f (u, v)) := isLocallyConstant_curry hf
  have hK₁ : IsCompact (Prod.fst '' tsupport f) := hf.2.isCompact.image continuous_fst
  have hzero : ∀ u, u ∉ Prod.fst '' tsupport f → (fun v => f (u, v)) = 0 := by
    intro u hu; funext v
    by_contra h
    exact hu ⟨(u, v), subset_tsupport _ h, rfl⟩
  have hfin : (Set.range (fun u => fun v => f (u, v))).Finite := by
    have : CompactSpace (Prod.fst '' tsupport f) := isCompact_iff_compactSpace.1 hK₁
    have h1 : (Set.range ((fun u => fun v => f (u, v)) ∘ ((↑) : Prod.fst '' tsupport f → X))).Finite :=
      (hF.comp_continuous continuous_subtype_val).range_finite
    refine (h1.union (Set.finite_singleton 0)).subset ?_
    rintro _ ⟨u, rfl⟩
    by_cases hu : u ∈ Prod.fst '' tsupport f
    · exact Or.inl ⟨⟨u, hu⟩, rfl⟩
    · exact Or.inr (hzero u hu)
  refine ⟨hfin.toFinset.erase 0, fun φ u => if (fun v => f (u, v)) = φ then 1 else 0, ?_, ?_, ?_⟩
  · intro φ hφ
    have hφ0 : φ ≠ 0 := Finset.ne_of_mem_erase hφ
    refine isTest_of_lc (hF.comp fun ψ => if ψ = φ then (1:ℂ) else 0) hK₁ ?_
    intro u hu
    by_contra hK
    apply hu
    show (if (fun v => f (u, v)) = φ then (1:ℂ) else 0) = 0
    rw [hzero u hK, if_neg (Ne.symm hφ0)]
  · intro φ hφ
    obtain ⟨u, rfl⟩ : φ ∈ Set.range (fun u => fun v => f (u, v)) :=
      (hfin.mem_toFinset).1 (Finset.mem_of_mem_erase hφ)
    exact isTest_fibre hf u
  · rintro ⟨u, v⟩
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · have h0 : (fun v => f (u, v)) = 0 := by
        by_contra h0
        exact h (Finset.mem_erase.2 ⟨h0, hfin.mem_toFinset.2 ⟨u, rfl⟩⟩)
      exact congrFun h0 v

/- English proof (translation)
Use function extensionality and compare the values at `p`. Establish `h1 : ∀ u, (fun v => f (u, v)) = ∑ j ∈ s, A j u • B j`. Introduce `u`. Use function extensionality and compare the values at `v`. Rewrite using `[hf (u, v)]`.

Simplify using `[Finset.sum_apply, smul_eq_mul]`. Establish `h2 : (fun u => W₂ gh.2 (fun v => f (u, v)) p.2) = ∑ j ∈ s, W₂ gh.2 (B j) p.2 • A j`. Use function extensionality and compare the values at `u`. Rewrite using `[h1 u, map_sum hW₂ gh.2 s _ _ hB, Finset.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `[smul_eq_mul, mul_comm]`. Rewrite using `[tensorRep_apply, h2, map_sum hW₁ gh.1 s _ _ hA, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[smul_eq_mul, mul_comm]`.
-/
theorem tensorRep_eq {G H : Type} [Group G] [Group H] {W₁ : G → (X → ℂ) → X → ℂ}
    {W₂ : H → (Y → ℂ) → Y → ℂ} (hW₁ : IsTestRep W₁) (hW₂ : IsTestRep W₂) {ι : Type} (s : Finset ι)
    (A : ι → X → ℂ) (B : ι → Y → ℂ) (hA : ∀ j ∈ s, IsTest (A j)) (hB : ∀ j ∈ s, IsTest (B j))
    (f : X × Y → ℂ) (hf : ∀ p : X × Y, f p = ∑ j ∈ s, A j p.1 * B j p.2) (gh : G × H) :
    tensorRep W₁ W₂ gh f = fun p => ∑ j ∈ s, W₁ gh.1 (A j) p.1 * W₂ gh.2 (B j) p.2 := by
  funext p
  have h1 : ∀ u, (fun v => f (u, v)) = ∑ j ∈ s, A j u • B j := by
    intro u; funext v; rw [hf (u, v)]; simp [Finset.sum_apply, smul_eq_mul]
  have h2 : (fun u => W₂ gh.2 (fun v => f (u, v)) p.2) = ∑ j ∈ s, W₂ gh.2 (B j) p.2 • A j := by
    funext u
    rw [h1 u, map_sum hW₂ gh.2 s _ _ hB, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [smul_eq_mul, mul_comm]
  rw [tensorRep_apply, h2, map_sum hW₁ gh.1 s _ _ hA, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [smul_eq_mul, mul_comm]

end Prod
end GlobalTheory.JR.WeilProd.TensorTest

namespace GlobalTheory.JR.WeilProd
open TensorTest

/- English proof (translation)
Introduce `hW₁ hW₂`. Establish `hslice : ∀ f : X × Y → ℂ, IsTest f → ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y)`. Introduce `f hf h y`. Take `⟨s, a, ha, hb, hfs⟩` from `decomp hf`. Establish `e : (fun u => W₂ h (fun v => f (u, v)) y) = ∑ φ ∈ s, W₂ h φ y • a φ`.

Use function extensionality and compare the values at `u`. Establish `h1 : (fun v => f (u, v)) = ∑ φ ∈ s, a φ u • φ`. Use function extensionality and compare the values at `v`. Rewrite using `[hfs (u, v)]`. Simplify using `[Finset.sum_apply, smul_eq_mul]`.

Rewrite using `[h1, map_sum hW₂ h s (fun φ => a φ u) (fun φ => φ) hb, Finset.sum_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun φ _ => ?_` and prove the remaining obligations. Simplify using `[smul_eq_mul, mul_comm]`. Rewrite using `[e]`. Conclude with `isTest_sum s _ fun φ hφ => isTest_smul _ (ha φ hφ)`.

Use `⟨⟨?_, ?_, ?_, ?_⟩, fun f hf => ⟨isTest_fibre hf, hslice f hf⟩⟩` and prove the remaining obligations. Introduce `gh f hf`. Take `⟨s, a, ha, hb, hfs⟩` from `decomp hf`. Rewrite using `[tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs gh]`. Conclude with `isTest_sum_fn s _ fun φ hφ => isTest_mul_prod (hW₁.1 _ _ (ha φ hφ)) (hW₂.1 _ _ (hb φ hφ))`.

Introduce `f hf`. Take `⟨s, a, ha, hb, hfs⟩` from `decomp hf`. Rewrite using `[tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs 1]`. Use function extensionality and compare the values at `p`. Rewrite using `[hfs p]`.

Use `Finset.sum_congr rfl fun φ hφ => ?_` and prove the remaining obligations. Simplify using `only [Prod.fst_one, Prod.snd_one]`. Rewrite using `[hW₁.2.1 _ (ha φ hφ), hW₂.2.1 _ (hb φ hφ)]`. Introduce `gh gh' f hf`. Take `⟨s, a, ha, hb, hfs⟩` from `decomp hf`.

Establish `hs' : ∀ p, tensorRep W₁ W₂ gh' f p = ∑ φ ∈ s, W₁ gh'.1 (a φ) p.1 * W₂ gh'.2 φ p.2` using `fun p => by`. Rewrite using `[tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs gh']`. Rewrite using `[tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs (gh * gh'), tensorRep_eq hW₁ hW₂ s (fun φ => W₁ gh'.1 (a φ)) (fun φ => W₂ gh'.2 φ) (fun φ hφ => hW₁.1 _ _ (ha φ hφ)) (fun φ hφ => hW₂.1 _ _ (hb φ hφ)) _ hs' gh]`. Use function extensionality and compare the values at `p`. Use `Finset.sum_congr rfl fun φ hφ => ?_` and prove the remaining obligations.

Simplify using `only [Prod.fst_mul, Prod.snd_mul]`. Rewrite using `[hW₁.2.2.1 _ _ _ (ha φ hφ), hW₂.2.2.1 _ _ _ (hb φ hφ)]`. Introduce `gh c f f' hf hf'`. Use function extensionality and compare the values at `p`. Establish `e2 : (fun u => W₂ gh.2 (fun v => (c • f + f') (u, v)) p.2) = c • (fun u => W₂ gh.2 (fun v => f (u, v)) p.2) + (fun u => W₂ gh.2 (fun v => f' (u, v)) p.2)`.

Use function extensionality and compare the values at `u`. Use `show W₂ gh.2 (c • (fun v => f (u, v)) + fun v => f' (u, v)) p.2 = _`. Rewrite using `[hW₂.2.2.2 gh.2 c _ _ (isTest_fibre hf u) (isTest_fibre hf' u)]`. Both sides reduce to the same expression. Rewrite using `[tensorRep_apply, e2, hW₁.2.2.2 gh.1 c _ _ (hslice f hf _ _) (hslice f' hf' _ _)]`.

Both sides reduce to the same expression.
-/
theorem isTestRep_tensorRep {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) :
    IsTestRep W₁ → IsTestRep W₂ → IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f →
      (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
  intro hW₁ hW₂
  have hslice : ∀ f : X × Y → ℂ, IsTest f → ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
    intro f hf h y
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    have e : (fun u => W₂ h (fun v => f (u, v)) y) = ∑ φ ∈ s, W₂ h φ y • a φ := by
      funext u
      have h1 : (fun v => f (u, v)) = ∑ φ ∈ s, a φ u • φ := by
        funext v; rw [hfs (u, v)]; simp [Finset.sum_apply, smul_eq_mul]
      rw [h1, map_sum hW₂ h s (fun φ => a φ u) (fun φ => φ) hb, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun φ _ => ?_
      simp [smul_eq_mul, mul_comm]
    rw [e]
    exact isTest_sum s _ fun φ hφ => isTest_smul _ (ha φ hφ)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun f hf => ⟨isTest_fibre hf, hslice f hf⟩⟩
  · intro gh f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs gh]
    exact isTest_sum_fn s _ fun φ hφ => isTest_mul_prod (hW₁.1 _ _ (ha φ hφ)) (hW₂.1 _ _ (hb φ hφ))
  · intro f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs 1]
    funext p
    rw [hfs p]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    simp only [Prod.fst_one, Prod.snd_one]
    rw [hW₁.2.1 _ (ha φ hφ), hW₂.2.1 _ (hb φ hφ)]
  · intro gh gh' f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    have hs' : ∀ p, tensorRep W₁ W₂ gh' f p = ∑ φ ∈ s, W₁ gh'.1 (a φ) p.1 * W₂ gh'.2 φ p.2 := fun p => by
      rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs gh']
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs (gh * gh'),
      tensorRep_eq hW₁ hW₂ s (fun φ => W₁ gh'.1 (a φ)) (fun φ => W₂ gh'.2 φ) (fun φ hφ => hW₁.1 _ _ (ha φ hφ))
        (fun φ hφ => hW₂.1 _ _ (hb φ hφ)) _ hs' gh]
    funext p
    refine Finset.sum_congr rfl fun φ hφ => ?_
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [hW₁.2.2.1 _ _ _ (ha φ hφ), hW₂.2.2.1 _ _ _ (hb φ hφ)]
  · intro gh c f f' hf hf'
    funext p
    have e2 : (fun u => W₂ gh.2 (fun v => (c • f + f') (u, v)) p.2) =
        c • (fun u => W₂ gh.2 (fun v => f (u, v)) p.2) + (fun u => W₂ gh.2 (fun v => f' (u, v)) p.2) := by
      funext u
      show W₂ gh.2 (c • (fun v => f (u, v)) + fun v => f' (u, v)) p.2 = _
      rw [hW₂.2.2.2 gh.2 c _ _ (isTest_fibre hf u) (isTest_fibre hf' u)]
      rfl
    rw [tensorRep_apply, e2, hW₁.2.2.2 gh.1 c _ _ (hslice f hf _ _) (hslice f' hf' _ _)]
    rfl

end GlobalTheory.JR.WeilProd
