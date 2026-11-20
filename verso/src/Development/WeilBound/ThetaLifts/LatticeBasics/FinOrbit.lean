import Development.WeilBound.ThetaLifts.LatticeBasics.HermAbs

noncomputable section

namespace GlobalTheory.ThK.Dbl.Herm

open scoped InnerProductSpace Cardinal
open PositivityTheory.ThKF.Abs Topology

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {P : Type} [AddCommGroup P] [Module ℂ P]

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace ℂ P`. Establish `: Countable (Module.Basis.ofVectorSpaceIndex ℂ P)` using `Cardinal.mk_le_aleph0_iff.1 (b.mk_eq_rank''.trans_le hr)`. Set `V : Finset (Module.Basis.ofVectorSpaceIndex ℂ P) → Submodule ℂ P` to `fun t => Submodule.span ℂ (t.image b)`. Establish `o : Continuous fun g => u (ρ g x)` using `continuous_pi fun h => by`. Simplify using `only [he]`.

Conclude with `(hc x).comp (continuous_const.mul continuous_id)`. Take `⟨t, g₀, h₀⟩` from `nonempty_interior_of_iUnion_of_closed (f := fun t => {g | ρ g x ∈ V t}) (fun t => by`. Establish `: IsClosed ((V t).map u : Set (G → ℂ))` using `Submodule.closed_of_finiteDimensional _`. Use `this.preimage o using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`.

Conclude with `⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, e⟩ => (hu e ▸ hy : ρ g x ∈ V t)⟩)`. Use the proof step `(Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨(b.repr (ρ g x)).support, by`. Simplify `b.mem_span_repr_support (ρ g x)⟩)` using `[V]`. Use `hC.induction_on ⟨⊥, inferInstance, by simp⟩ (fun s s' h ⟨W, h1, h2⟩ => ⟨W, h1, fun g hg => h2 g (h hg)⟩) (fun s s' ⟨W, h1, h2⟩ ⟨W', h1', h2'⟩ => ⟨W ⊔ W', inferInstance, fun g hg => hg.elim (fun h => Submodule.mem_sup_left (h2 g h)) fun h => Submodule.mem_sup_right (h2' g h)⟩) fun …` and prove the remaining obligations. Use `⟨(fun g => g₀ * k⁻¹ * g) ⁻¹' {g | ρ g x ∈ V t}, mem_nhdsWithin_of_mem_nhds ((continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 h₀)), (V t).map (ρ (k * g₀⁻¹)), inferInstance, fun g hg => ⟨_, hg, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Use `congr 2`. Use `group`.
-/
theorem fin_orbit [BaireSpace G] (ρ : G →* Module.End ℂ P) (u : P →ₗ[ℂ] (G → ℂ)) (hu : Function.Injective u)
    (hc : ∀ x, Continuous (u x)) (he : ∀ g x h, u (ρ g x) h = u x (h * g)) (hr : Module.rank ℂ P ≤ ℵ₀) (x : P) {C : Set G}
    (hC : IsCompact C) : ∃ V : Submodule ℂ P, FiniteDimensional ℂ V ∧ ∀ g ∈ C, ρ g x ∈ V := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ P
  have : Countable (Module.Basis.ofVectorSpaceIndex ℂ P) := Cardinal.mk_le_aleph0_iff.1 (b.mk_eq_rank''.trans_le hr)
  let V : Finset (Module.Basis.ofVectorSpaceIndex ℂ P) → Submodule ℂ P := fun t => Submodule.span ℂ (t.image b)
  have o : Continuous fun g => u (ρ g x) := continuous_pi fun h => by
    simp only [he]; exact (hc x).comp (continuous_const.mul continuous_id)
  obtain ⟨t, g₀, h₀⟩ := nonempty_interior_of_iUnion_of_closed (f := fun t => {g | ρ g x ∈ V t}) (fun t => by
      have : IsClosed ((V t).map u : Set (G → ℂ)) := Submodule.closed_of_finiteDimensional _
      convert this.preimage o using 1
      ext g
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, e⟩ => (hu e ▸ hy : ρ g x ∈ V t)⟩)
    (Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨(b.repr (ρ g x)).support, by
      simpa [V] using b.mem_span_repr_support (ρ g x)⟩)
  refine hC.induction_on ⟨⊥, inferInstance, by simp⟩ (fun s s' h ⟨W, h1, h2⟩ => ⟨W, h1, fun g hg => h2 g (h hg)⟩)
    (fun s s' ⟨W, h1, h2⟩ ⟨W', h1', h2'⟩ => ⟨W ⊔ W', inferInstance, fun g hg =>
      hg.elim (fun h => Submodule.mem_sup_left (h2 g h)) fun h => Submodule.mem_sup_right (h2' g h)⟩) fun k _ => ?_
  refine ⟨(fun g => g₀ * k⁻¹ * g) ⁻¹' {g | ρ g x ∈ V t}, mem_nhdsWithin_of_mem_nhds
    ((continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using mem_interior_iff_mem_nhds.1 h₀)),
    (V t).map (ρ (k * g₀⁻¹)), inferInstance, fun g hg => ⟨_, hg, ?_⟩⟩
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/- English proof (translation)
Distinguish the cases in `h0 : ∀ x, u x = 0`. Conclude with `⟨0, fun x y => by rw [b1 (h0 x)]; simp⟩`. Use `push Not at h0`. Take `⟨f, hf⟩` from `h0`. Establish `c1 : LinearMap.ker u ≤ c.ker` using `fun x hx => LinearMap.ext fun y => by`.

Rewrite using `[← hs, show c y x = 0 from LinearMap.congr_fun (c2 hx) y]`. Simplify using the standard rewrite rules. Establish `st : ∀ g, LinearMap.ker u ≤ (LinearMap.ker u).comap (ρ g)` using `fun g x hx => funext fun h => by`. Rewrite using `[he, show u x = 0 from hx]`. Both sides reduce to the same expression.

Set `U` to `P ⧸ LinearMap.ker u`. Set `π : P →ₗ[ℂ] U` to `(LinearMap.ker u).mkQ`. Establish `sj : ∀ z : U, ∃ x, π x = z` using `(LinearMap.ker u).mkQ_surjective`. Set `b' : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ` to `LinearMap.liftQ₂ _ _ b b1 b2`. Set `c' : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ` to `LinearMap.liftQ₂ _ _ c c1 c2`.

Set `ρ' : G →* Module.End ℂ U` to `{ toFun := fun g => Submodule.mapQ _ _ (ρ g) (st g) map_one' := LinearMap.ext fun z => by obtain ⟨x, rfl⟩ := sj z; exact congrArg π (by simp) map_mul' := fun g h => LinearMap.ext fun z => by obtain ⟨x, rfl⟩ := sj z; exact congrArg π (by simp) }`. Set `u' : U →ₗ[ℂ] (G → ℂ)` to `(LinearMap.ker u).liftQ u le_rfl`. Establish `iu : Function.Injective u'` using `LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)`. Set `core : InnerProductSpace.Core ℂ U` to `{ inner := fun x y => c' x y conj_inner_symm := fun z w => by obtain ⟨x, rfl⟩ := sj z; obtain ⟨y, rfl⟩ := sj w; exact hs x y re_inner_nonneg := fun z => by obtain ⟨x, rfl⟩ := sj z; exact hp x add_left := fun x y z => by simp smul_left := fun x y r => by simp definite := fun z hz …`. Use `letI : NormedAddCommGroup U := core.toNormedAddCommGroup`.

Use `letI : InnerProductSpace ℂ U := InnerProductSpace.ofCore core.toCore`. Take `⟨t, -, ht⟩` from `hΩ.elim_nhds_subcover (fun g => (fun h => g⁻¹ * h) ⁻¹' K) fun g _ => (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (hK.mem_nhds (by simpa using K.one_mem))`. Take `⟨z, lam, hz, e⟩` from `exists_eigen (U := U) (ρ'.comp K.subtype) (fun k z w => by obtain ⟨x, rfl⟩ := sj z; obtain ⟨y, rfl⟩ := sj w; exact hi k x y) (fun z => by`. Take `⟨V, h1, h2⟩` from `fin_orbit ρ' u' iu (fun z => by obtain ⟨x, rfl⟩ := sj z; exact hc x) (fun g z h => by obtain ⟨x, rfl⟩ := sj z; exact he g x h) (u.quotKerEquivRange.rank_eq.trans_le hr) z hK'`. Conclude with `Submodule.finiteDimensional_of_le (S₂ := V) (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h2 k k.2)))`.

Use the proof step `(fun i : t => LinearMap.proj i.1 ∘ₗ u')`. Use the proof step `(fun z hz => by`. Take `⟨x, rfl⟩` from `sj z`. Use `(Submodule.Quotient.mk_eq_zero _).2 (funext fun g => ?_)` and prove the remaining obligations. Take `⟨g', h1, h2⟩` from `cov g`.

Take `⟨i, hi, h3⟩` from `Set.mem_iUnion₂.1 (ht h1)`. Establish `: u (ρ (i⁻¹ * g') x) i = 0` using `hz ⟨i, hi⟩ ⟨_, h3⟩`. Rewrite using `[he, mul_inv_cancel_left, ← h2] at this)` and apply the resulting hypothesis. Use the proof step `b' (fun k z w => by obtain ⟨x, rfl⟩ := sj z; obtain ⟨y, rfl⟩ := sj w; exact hb k x y) (π f)`. Use the proof step `(fun h => hf ((Submodule.Quotient.mk_eq_zero _).1 h))`.

Take `⟨x₀, rfl⟩` from `sj z`. Set `N : Submodule ℂ P` to `LinearMap.ker (b - lam • c)`. Establish `mN : ∀ x, x ∈ N ↔ ∀ y, b x y = lam * c x y` using `fun x => by`. Simplify using `[N, LinearMap.ext_iff, sub_eq_zero]`. Use `(irr N (fun x hx => (mN x).2 fun y => ?_) fun g x hx => (mN _).2 fun y => ?_).elim (fun h => absurd ((Submodule.Quotient.mk_eq_zero _).2 (h ((mN x₀).2 fun y => e (π y)))) hz) fun h => ⟨lam, fun x => (mN x).1 (h ▸ trivial)⟩` and prove the remaining obligations.

Rewrite using `[b1 hx, c1 hx]`. Simplify using the standard rewrite rules. Rewrite using `[show y = ρ g (ρ g⁻¹ y) by rw [← Module.End.mul_apply, ← map_mul]; simp, hb, hi, (mN x).1 hx]`.
-/
theorem line [LocallyCompactSpace G] [T2Space G] (ρ : G →* Module.End ℂ P) (u : P →ₗ[ℂ] (G → ℂ)) (hc : ∀ x, Continuous (u x))
    (he : ∀ g x h, u (ρ g x) h = u x (h * g)) (hr : Module.rank ℂ (LinearMap.range u) ≤ ℵ₀)
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (hK' : IsCompact (K : Set G)) {Ω : Set G} (hΩ : IsCompact Ω)
    (cov : ∀ g, ∃ g' ∈ Ω, ∀ x, u x g = u x g') (b c : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ)
    (hb : ∀ g x y, b (ρ g x) (ρ g y) = b x y) (hi : ∀ g x y, c (ρ g x) (ρ g y) = c x y)
    (hs : ∀ x y, starRingEnd ℂ (c y x) = c x y) (hp : ∀ x, 0 ≤ (c x x).re) (hd : ∀ x, c x x = 0 → u x = 0)
    (b1 : LinearMap.ker u ≤ b.ker) (b2 : LinearMap.ker u ≤ b.flip.ker) (c2 : LinearMap.ker u ≤ c.flip.ker)
    (irr : ∀ N : Submodule ℂ P, LinearMap.ker u ≤ N → (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N ≤ LinearMap.ker u ∨ N = ⊤) :
    ∃ lam : ℂ, ∀ x y, b x y = lam * c x y := by
  by_cases h0 : ∀ x, u x = 0
  · exact ⟨0, fun x y => by rw [b1 (h0 x)]; simp⟩
  push Not at h0
  obtain ⟨f, hf⟩ := h0
  have c1 : LinearMap.ker u ≤ c.ker := fun x hx => LinearMap.ext fun y => by
    rw [← hs, show c y x = 0 from LinearMap.congr_fun (c2 hx) y]; simp
  have st : ∀ g, LinearMap.ker u ≤ (LinearMap.ker u).comap (ρ g) := fun g x hx => funext fun h => by
    rw [he, show u x = 0 from hx]; rfl
  let U := P ⧸ LinearMap.ker u
  let π : P →ₗ[ℂ] U := (LinearMap.ker u).mkQ
  have sj : ∀ z : U, ∃ x, π x = z := (LinearMap.ker u).mkQ_surjective
  let b' : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ := LinearMap.liftQ₂ _ _ b b1 b2
  let c' : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ := LinearMap.liftQ₂ _ _ c c1 c2
  let ρ' : G →* Module.End ℂ U :=
    { toFun := fun g => Submodule.mapQ _ _ (ρ g) (st g)
      map_one' := LinearMap.ext fun z => by obtain ⟨x, rfl⟩ := sj z; exact congrArg π (by simp)
      map_mul' := fun g h => LinearMap.ext fun z => by obtain ⟨x, rfl⟩ := sj z; exact congrArg π (by simp) }
  let u' : U →ₗ[ℂ] (G → ℂ) := (LinearMap.ker u).liftQ u le_rfl
  have iu : Function.Injective u' := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  let core : InnerProductSpace.Core ℂ U :=
    { inner := fun x y => c' x y
      conj_inner_symm := fun z w => by obtain ⟨x, rfl⟩ := sj z; obtain ⟨y, rfl⟩ := sj w; exact hs x y
      re_inner_nonneg := fun z => by obtain ⟨x, rfl⟩ := sj z; exact hp x
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun z hz => by obtain ⟨x, rfl⟩ := sj z; exact (Submodule.Quotient.mk_eq_zero _).2 (hd x hz) }
  letI : NormedAddCommGroup U := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ U := InnerProductSpace.ofCore core.toCore
  obtain ⟨t, -, ht⟩ := hΩ.elim_nhds_subcover (fun g => (fun h => g⁻¹ * h) ⁻¹' K) fun g _ =>
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (hK.mem_nhds (by simpa using K.one_mem))
  obtain ⟨z, lam, hz, e⟩ := exists_eigen (U := U) (ρ'.comp K.subtype)
    (fun k z w => by obtain ⟨x, rfl⟩ := sj z; obtain ⟨y, rfl⟩ := sj w; exact hi k x y)
    (fun z => by
      obtain ⟨V, h1, h2⟩ := fin_orbit ρ' u' iu (fun z => by obtain ⟨x, rfl⟩ := sj z; exact hc x)
        (fun g z h => by obtain ⟨x, rfl⟩ := sj z; exact he g x h) (u.quotKerEquivRange.rank_eq.trans_le hr) z hK'
      exact Submodule.finiteDimensional_of_le (S₂ := V) (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact h2 k k.2)))
    (fun i : t => LinearMap.proj i.1 ∘ₗ u')
    (fun z hz => by
      obtain ⟨x, rfl⟩ := sj z
      refine (Submodule.Quotient.mk_eq_zero _).2 (funext fun g => ?_)
      obtain ⟨g', h1, h2⟩ := cov g
      obtain ⟨i, hi, h3⟩ := Set.mem_iUnion₂.1 (ht h1)
      have : u (ρ (i⁻¹ * g') x) i = 0 := hz ⟨i, hi⟩ ⟨_, h3⟩
      rwa [he, mul_inv_cancel_left, ← h2] at this)
    b' (fun k z w => by obtain ⟨x, rfl⟩ := sj z; obtain ⟨y, rfl⟩ := sj w; exact hb k x y) (π f)
    (fun h => hf ((Submodule.Quotient.mk_eq_zero _).1 h))
  obtain ⟨x₀, rfl⟩ := sj z
  let N : Submodule ℂ P := LinearMap.ker (b - lam • c)
  have mN : ∀ x, x ∈ N ↔ ∀ y, b x y = lam * c x y := fun x => by
    simp [N, LinearMap.ext_iff, sub_eq_zero]
  refine (irr N (fun x hx => (mN x).2 fun y => ?_) fun g x hx => (mN _).2 fun y => ?_).elim
    (fun h => absurd ((Submodule.Quotient.mk_eq_zero _).2 (h ((mN x₀).2 fun y => e (π y)))) hz)
    fun h => ⟨lam, fun x => (mN x).1 (h ▸ trivial)⟩
  · rw [b1 hx, c1 hx]; simp
  · rw [show y = ρ g (ρ g⁻¹ y) by rw [← Module.End.mul_apply, ← map_mul]; simp, hb, hi, (mN x).1 hx]

end GlobalTheory.ThK.Dbl.Herm

end
