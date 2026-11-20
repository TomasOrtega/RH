import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

noncomputable section
namespace GlobalTheory.IndependentSpanDual
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam

variable {k : Type} [Field k]

/- English proof (translation)
Use `haveI : Module.Finite k⟦X⟧ P := Module.Finite.iff_fg.mpr hP`. Use `haveI : NoZeroSMulDivisors k⟦X⟧ Q := by`. Use `⟨fun {c x} h => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Establish `hc : algebraMap k⟦X⟧ k⸨X⸩ c ≠ 0`. Introduce `h0`. Conclude with `hne.1 ((IsFractionRing.injective k⟦X⟧ k⸨X⸩) (by rw [h0, map_zero]))`. Establish `h' : algebraMap k⟦X⟧ k⸨X⸩ c • x = 0`. Rewrite using `[algebraMap_smul]`.

Conclude with `h`. Conclude with `hne.2 ((smul_eq_zero.mp h').resolve_left hc)`. Use `haveI : Module.Free k⟦X⟧ P := Module.free_of_finite_type_torsion_free'`. Set `b` to `Module.Free.chooseBasis k⟦X⟧ P`. Use `⟨Module.Free.ChooseBasisIndex k⟦X⟧ P, inferInstance, fun i => (b i : Q), ?_, ?_⟩` and prove the remaining obligations.

Establish `hli : LinearIndependent k⟦X⟧ (P.subtype ∘ b)` using `b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)`. Conclude with `(LinearIndependent.iff_fractionRing k⟦X⟧ k⸨X⸩).mp hli`. Establish `hr : Set.range (fun i => (b i : Q)) = P.subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem exists_indep_span {Q : Type} [AddCommGroup Q] [Module k⸨X⸩ Q] [Module k⟦X⟧ Q]
    [IsScalarTower k⟦X⟧ k⸨X⸩ Q] {P : Submodule k⟦X⟧ Q} (hP : P.FG) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → Q), LinearIndependent k⸨X⸩ e ∧
      Submodule.span k⟦X⟧ (Set.range e) = P := by
  classical
  haveI : Module.Finite k⟦X⟧ P := Module.Finite.iff_fg.mpr hP
  haveI : NoZeroSMulDivisors k⟦X⟧ Q := by
    refine ⟨fun {c x} h => ?_⟩
    by_contra hne
    push_neg at hne
    have hc : algebraMap k⟦X⟧ k⸨X⸩ c ≠ 0 := by
      intro h0
      exact hne.1 ((IsFractionRing.injective k⟦X⟧ k⸨X⸩) (by rw [h0, map_zero]))
    have h' : algebraMap k⟦X⟧ k⸨X⸩ c • x = 0 := by
      rw [algebraMap_smul]
      exact h
    exact hne.2 ((smul_eq_zero.mp h').resolve_left hc)
  haveI : Module.Free k⟦X⟧ P := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis k⟦X⟧ P
  refine ⟨Module.Free.ChooseBasisIndex k⟦X⟧ P, inferInstance, fun i => (b i : Q), ?_, ?_⟩
  · have hli : LinearIndependent k⟦X⟧ (P.subtype ∘ b) :=
      b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
    exact (LinearIndependent.iff_fractionRing k⟦X⟧ k⸨X⸩).mp hli
  · have hr : Set.range (fun i => (b i : Q)) = P.subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace k⸨X⸩ V`. Set `c` to `Module.Basis.mk (D.linearIndependent_φ i b) (D.span_φ i b).ge`. Use `⟨c.constr k⸨X⸩ fun j => R.φ (t (b j)), fun x => ?_⟩` and prove the remaining obligations. Establish `hx : x ∈ Submodule.span k⸨X⸩ (Set.range b)` using `by rw [b.span_eq]; trivial`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Establish `hc : D.φ i (b j) = c j` using `(Module.Basis.mk_apply (D.linearIndependent_φ i b) (D.span_φ i b).ge j).symm`. Rewrite using `[hc, Module.Basis.constr_basis]`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz => simp only [map_add, hy, hz]`. Consider the case `smul a y _ hy => rw [D.φ_semi i a y, map_smul, map_smul, hy, smul_eq_mul, smul_eq_mul, map_mul]`.
-/
theorem exists_form {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k V] {l n : ℕ} {R : RingPG k l}
    (D : ModPG R n V) (i : ZMod n) (t : V →ₗ[k⸨X⸩] k⸨X⸩) :
    ∃ u : V →ₗ[k⸨X⸩] k⸨X⸩, ∀ x, u (D.φ i x) = R.φ (t x) := by
  let b := Module.Basis.ofVectorSpace k⸨X⸩ V
  let c := Module.Basis.mk (D.linearIndependent_φ i b) (D.span_φ i b).ge
  refine ⟨c.constr k⸨X⸩ fun j => R.φ (t (b j)), fun x => ?_⟩
  have hx : x ∈ Submodule.span k⸨X⸩ (Set.range b) := by rw [b.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    have hc : D.φ i (b j) = c j :=
      (Module.Basis.mk_apply (D.linearIndependent_φ i b) (D.span_φ i b).ge j).symm
    rw [hc, Module.Basis.constr_basis]
  | zero => simp
  | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | smul a y _ hy => rw [D.φ_semi i a y, map_smul, map_smul, hy, smul_eq_mul, smul_eq_mul, map_mul]

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_extend ((Module.Basis.span he).coord j)`. Use `⟨g, fun m => ?_⟩` and prove the remaining obligations. Establish `hm : e m = (Submodule.span K (Set.range e)).subtype (Module.Basis.span he m)`. Rewrite using `[Module.Basis.span_apply]`. Both sides reduce to the same expression.

Rewrite using `[hm, ← LinearMap.comp_apply, hg, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`.
-/
theorem exists_dual {K Q ι : Type} [Field K] [AddCommGroup Q] [Module K Q] [DecidableEq ι] {e : ι → Q}
    (he : LinearIndependent K e) (j : ι) :
    ∃ t : Q →ₗ[K] K, ∀ m, t (e m) = if m = j then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span he).coord j)
  refine ⟨g, fun m => ?_⟩
  have hm : e m = (Submodule.span K (Set.range e)).subtype (Module.Basis.span he m) := by
    rw [Module.Basis.span_apply]
    rfl
  rw [hm, ← LinearMap.comp_apply, hg, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `swap`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Express the relevant statement in the definitionally equal form `g (D'.φ i x) ∈ pull (D.φ i) N`.

Rewrite using `[h]`. Conclude with `Submodule.subset_span ⟨_, hx, rfl⟩`. Set `π` to `(LinearMap.range f).mkQ`. Take `⟨ι, _, e, he, hsp⟩` from `exists_indep_span (hN.map (π.restrictScalars k⟦X⟧))`. Establish `hlift : ∀ j, ∃ s ∈ N, π s = e j` using `fun j => by`.

Establish `: e j ∈ N.map (π.restrictScalars k⟦X⟧)` using `hsp ▸ Submodule.subset_span ⟨j, rfl⟩`. Conclude with `this`. Use `choose s hsN hs using hlift`. Establish `hle : pull (D.φ i) N ≤ (pull (D'.φ i) (N.comap (f.restrictScalars k⟦X⟧))).map (g.restrictScalars k⟦X⟧) ⊔ Submodule.span k⟦X⟧ (Set.range fun j => D.φ i (s j))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx' : π x ∈ Submodule.span k⟦X⟧ (Set.range e)` using `hsp ▸ ⟨x, hx, rfl⟩`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun k⟦X⟧).1 hx'`. Establish `h0 : x - ∑ j, a j • s j ∈ LinearMap.range f`. Rewrite using `[← Submodule.ker_mkQ (LinearMap.range f), LinearMap.mem_ker]`.

Express the relevant statement in the definitionally equal form `(π.restrictScalars k⟦X⟧) _ = 0`. Rewrite using `[map_sub, map_sum, sub_eq_zero]`. Simplify using `only [map_smul, LinearMap.restrictScalars_apply, hs, ha]`. Take `⟨w, hw⟩` from `h0`. Establish `hwN : f w ∈ N` using `hw ▸ N.sub_mem hx (N.sum_mem fun j _ => N.smul_mem _ (hsN j))`.

Establish `hx2 : x = f w + ∑ j, a j • s j` using `by rw [hw, sub_add_cancel]`. Rewrite using `[hx2, map_add, map_sum, ← h]`. Use `Submodule.add_mem_sup ⟨_, Submodule.subset_span ⟨w, hwN, rfl⟩, rfl⟩ (Submodule.sum_mem _ fun j _ => ?_)` and prove the remaining obligations. Take `⟨b, hb⟩` from `R.φ_int (a j)`. Establish `: D.φ i (a j • s j) = b • D.φ i (s j)`.

Rewrite using `[← algebraMap_smul k⸨X⸩ (a j), D.φ_semi i, ← algebraMap_smul k⸨X⸩ b]`. Conclude with `congrArg (· • D.φ i (s j)) hb`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Introduce `y hy`.

Take `⟨_, ⟨p, hp, rfl⟩, q, hq, hpq⟩` from `Submodule.mem_sup.1 (hle hy)`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun k⟦X⟧).1 hq`. Establish `hq' : ∑ j, a j • D.φ i (s j) = g (y - p)`. Rewrite using `[map_sub, eq_sub_iff_add_eq']`. Conclude with `hpq`.

Establish `ha : ∀ j, algebraMap k⟦X⟧ k⸨X⸩ (a j) = 0` using `fun j => by`. Take `⟨t, ht⟩` from `exists_dual he j`. Take `⟨u, hu⟩` from `exists_form D i (t.comp π)`. Establish `hug : u.comp g = 0`. Use `LinearMap.ext_on_range (D'.etale i) fun x => ?_` and prove the remaining obligations.

Establish `: π (f x) = 0` using `(Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩`. Rewrite using `[LinearMap.comp_apply, h, hu, LinearMap.comp_apply, this, map_zero, map_zero, LinearMap.zero_apply]`. Establish `h1 : u (∑ m, a m • D.φ i (s m)) = 0`. Rewrite using `[hq']`. Conclude with `LinearMap.congr_fun hug _`.

Establish `h2 : ∀ m, u (a m • D.φ i (s m)) = if m = j then algebraMap k⟦X⟧ k⸨X⸩ (a m) else 0` using `fun m => by`. Rewrite using `[← algebraMap_smul k⸨X⸩ (a m), map_smul, hu, LinearMap.comp_apply, hs, ht]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite `h1` using `[map_sum]`. Simplify `h1` using `[h2]`.

Establish `hz : g (y - p) = 0`. Rewrite using `[← hq']`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul k⸨X⸩ (a j), ha, zero_smul]`. Establish `: y = p` using `sub_eq_zero.1 (hg (hz.trans (map_zero g).symm))`.

Rewrite using `[this]`. Conclude with `hp`.
-/
theorem comap_pull {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
    [IsScalarTower k⟦X⟧ k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W]
    [IsScalarTower k⟦X⟧ k⸨X⸩ W] [Module k V] [Module k W] {l n : ℕ} {R : RingPG k l}
    (D : ModPG R n V) (D' : ModPG R n W) (i : ZMod n) (f g : W →ₗ[k⸨X⸩] V)
    (_hf : Function.Injective f) (hg : Function.Injective g)
    (h : ∀ x, g (D'.φ i x) = D.φ i (f x)) {N : Submodule k⟦X⟧ V} (hN : N.FG) :
    (pull (D.φ i) N).comap (g.restrictScalars k⟦X⟧) = pull (D'.φ i) (N.comap (f.restrictScalars k⟦X⟧)) := by
  classical
  apply le_antisymm
  swap
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    change g (D'.φ i x) ∈ pull (D.φ i) N
    rw [h]
    exact Submodule.subset_span ⟨_, hx, rfl⟩
  let π := (LinearMap.range f).mkQ
  obtain ⟨ι, _, e, he, hsp⟩ := exists_indep_span (hN.map (π.restrictScalars k⟦X⟧))
  have hlift : ∀ j, ∃ s ∈ N, π s = e j := fun j => by
    have : e j ∈ N.map (π.restrictScalars k⟦X⟧) := hsp ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  choose s hsN hs using hlift

  have hle : pull (D.φ i) N ≤ (pull (D'.φ i) (N.comap (f.restrictScalars k⟦X⟧))).map (g.restrictScalars k⟦X⟧) ⊔
      Submodule.span k⟦X⟧ (Set.range fun j => D.φ i (s j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : π x ∈ Submodule.span k⟦X⟧ (Set.range e) := hsp ▸ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun k⟦X⟧).1 hx'
    have h0 : x - ∑ j, a j • s j ∈ LinearMap.range f := by
      rw [← Submodule.ker_mkQ (LinearMap.range f), LinearMap.mem_ker]
      change (π.restrictScalars k⟦X⟧) _ = 0
      rw [map_sub, map_sum, sub_eq_zero]
      simp only [map_smul, LinearMap.restrictScalars_apply, hs, ha]
    obtain ⟨w, hw⟩ := h0
    have hwN : f w ∈ N := hw ▸ N.sub_mem hx (N.sum_mem fun j _ => N.smul_mem _ (hsN j))
    have hx2 : x = f w + ∑ j, a j • s j := by rw [hw, sub_add_cancel]
    rw [hx2, map_add, map_sum, ← h]
    refine Submodule.add_mem_sup ⟨_, Submodule.subset_span ⟨w, hwN, rfl⟩, rfl⟩
      (Submodule.sum_mem _ fun j _ => ?_)
    obtain ⟨b, hb⟩ := R.φ_int (a j)
    have : D.φ i (a j • s j) = b • D.φ i (s j) := by
      rw [← algebraMap_smul k⸨X⸩ (a j), D.φ_semi i, ← algebraMap_smul k⸨X⸩ b]
      exact congrArg (· • D.φ i (s j)) hb
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  intro y hy
  obtain ⟨_, ⟨p, hp, rfl⟩, q, hq, hpq⟩ := Submodule.mem_sup.1 (hle hy)
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k⟦X⟧).1 hq
  have hq' : ∑ j, a j • D.φ i (s j) = g (y - p) := by
    rw [map_sub, eq_sub_iff_add_eq']
    exact hpq
  have ha : ∀ j, algebraMap k⟦X⟧ k⸨X⸩ (a j) = 0 := fun j => by
    obtain ⟨t, ht⟩ := exists_dual he j
    obtain ⟨u, hu⟩ := exists_form D i (t.comp π)
    have hug : u.comp g = 0 := by
      refine LinearMap.ext_on_range (D'.etale i) fun x => ?_
      have : π (f x) = 0 := (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
      rw [LinearMap.comp_apply, h, hu, LinearMap.comp_apply, this, map_zero, map_zero, LinearMap.zero_apply]
    have h1 : u (∑ m, a m • D.φ i (s m)) = 0 := by
      rw [hq']; exact LinearMap.congr_fun hug _
    have h2 : ∀ m, u (a m • D.φ i (s m)) = if m = j then algebraMap k⟦X⟧ k⸨X⸩ (a m) else 0 := fun m => by
      rw [← algebraMap_smul k⸨X⸩ (a m), map_smul, hu, LinearMap.comp_apply, hs, ht]
      split_ifs <;> simp
    rw [map_sum] at h1
    simpa [h2] using h1
  have hz : g (y - p) = 0 := by
    rw [← hq']
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← algebraMap_smul k⸨X⸩ (a j), ha, zero_smul]
  have : y = p := sub_eq_zero.1 (hg (hz.trans (map_zero g).symm))
  rw [this]
  exact hp

end GlobalTheory.IndependentSpanDual
