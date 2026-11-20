import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Use `⟨n.projection b h.symm, fun x => Submodule.projection_apply_mem _ x, fun x => ?_⟩` and prove the remaining obligations. Establish `e` using `Submodule.projection_add_projection_eq_self h.symm x`. Establish `hm : b.projection n h x ∈ b` using `Submodule.projection_apply_mem _ x`. Establish `: n.projection b h.symm x - x = -(b.projection n h x)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[this]`. Conclude with `b.neg_mem hm`.
-/
private theorem exProj {k W : Type} [Field k] [AddCommGroup W] [Module k W] (b n : Submodule k W)
    (h : IsCompl b n) : ∃ P : W →ₗ[k] W, (∀ x, P x ∈ n) ∧ ∀ x, P x - x ∈ b := by
  refine ⟨n.projection b h.symm, fun x => Submodule.projection_apply_mem _ x, fun x => ?_⟩
  have e := Submodule.projection_add_projection_eq_self h.symm x
  have hm : b.projection n h x ∈ b := Submodule.projection_apply_mem _ x
  have : n.projection b h.symm x - x = -(b.projection n h x) := by
    calc n.projection b h.symm x - x
        = n.projection b h.symm x - (n.projection b h.symm x + b.projection n h x) := by rw [e]
      _ = -(b.projection n h x) := by abel
  rw [this]
  exact b.neg_mem hm

/- English proof (translation)
Use `haveI hK : Module.Finite k (LinearMap.ker e) := Module.Finite.of_injective j hj`. Use `haveI hT : Module.Finite k T := by`. Rewrite using `[← Module.rank_lt_aleph0_iff, ← LinearMap.rank_range_add_rank_ker e]`. Conclude with `Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 k _) (Module.rank_lt_aleph0 k _)`. Establish `r1` using `LinearMap.finrank_range_add_finrank_ker e`.

Establish `r2` using `Submodule.finrank_le (LinearMap.range e)`. Establish `r3` using `Submodule.finrank_quotient_add_finrank t`. Establish `r4` using `LinearMap.finrank_le_finrank_of_injective hj`. Establish `r5` using `LinearMap.finrank_range_add_finrank_ker q`. Establish `r6 : Module.finrank k (LinearMap.range q) = Module.finrank k H`.

Rewrite using `[LinearMap.range_eq_top.mpr hq, finrank_top]`. Establish `hfq : LinearMap.range f ≤ LinearMap.ker q`. Introduce and unpack `_ ⟨X, rfl⟩`. Conclude with `hf X`. Establish `r7` using `Submodule.finrank_mono hfq`.

Establish `r8` using `LinearMap.finrank_range_add_finrank_ker f`. Establish `r9` using `Submodule.finrank_mono h0`. Use linear arithmetic over natural numbers and integers.
-/
private theorem dimLem {k W T H A : Type} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    [AddCommGroup T] [Module k T] [AddCommGroup H] [Module k H] [AddCommGroup A] [Module k A] [Module.Finite k A]
    (t H0 : Submodule k W) (e : T →ₗ[k] W ⧸ t) (j : LinearMap.ker e →ₗ[k] A) (hj : Function.Injective j)
    (q : T →ₗ[k] H) (hq : Function.Surjective q) (f : W →ₗ[k] T) (hf : ∀ X, q (f X) = 0)
    (h0 : LinearMap.ker f ≤ H0) :
    Module.finrank k H + Module.finrank k t ≤ Module.finrank k A + Module.finrank k H0 := by
  haveI hK : Module.Finite k (LinearMap.ker e) := Module.Finite.of_injective j hj
  haveI hT : Module.Finite k T := by
    rw [← Module.rank_lt_aleph0_iff, ← LinearMap.rank_range_add_rank_ker e]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 k _) (Module.rank_lt_aleph0 k _)
  have r1 := LinearMap.finrank_range_add_finrank_ker e
  have r2 := Submodule.finrank_le (LinearMap.range e)
  have r3 := Submodule.finrank_quotient_add_finrank t
  have r4 := LinearMap.finrank_le_finrank_of_injective hj
  have r5 := LinearMap.finrank_range_add_finrank_ker q
  have r6 : Module.finrank k (LinearMap.range q) = Module.finrank k H := by
    rw [LinearMap.range_eq_top.mpr hq, finrank_top]
  have hfq : LinearMap.range f ≤ LinearMap.ker q := by
    rintro _ ⟨X, rfl⟩
    exact hf X
  have r7 := Submodule.finrank_mono hfq
  have r8 := LinearMap.finrank_range_add_finrank_ker f
  have r9 := Submodule.finrank_mono h0
  omega

/- English proof (translation)
Introduce `k G W V _ _ _ _ _ _ Gv _ loc ρ b n g0 t hlc hstab hcompl hfin`. Use `choose P hPn hPb using fun v => exProj (b v) (n v) (hcompl v)`. Establish `hPb' : ∀ v x, x - P v x ∈ b v` using `fun v x => by`. Simplify using `using (b v).neg_mem (hPb v x)`. Establish `hloc : ∀ v (s : Gv v) (y : W), y ∈ b v → ρ (loc v s) y - y ∈ b v` using `fun v s y hy => (b v).sub_mem (hstab v s y hy) hy`.

Use `set S : Submodule k ((G → W) × (V → W)) := Fr.Z1C loc ρ b ⊓ Submodule.comap (LinearMap.snd k (G → W) (V → W)) (Submodule.pi Set.univ n) with hSd`. Set `q : S →ₗ[k] Fr.H1C loc ρ b` to `(Submodule.mkQ _) ∘ₗ Submodule.inclusion (inf_le_left : S ≤ Fr.Z1C loc ρ b)`. Establish `hq : Function.Surjective q`. Introduce `y`. Take `⟨z, rfl⟩` from `Submodule.mkQ_surjective _ y`.

Take `⟨⟨c, x⟩, hz⟩` from `z`. Take `⟨hz1, hz2, hz3⟩` from `hz`. Establish `hmem : ((c, fun v => P v (x v)) : (G → W) × (V → W)) ∈ S`. Use `⟨⟨hz1, hz2, fun v s => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `hz3 v s`.

Establish `h2` using `hloc v s _ (hPb v (x v))`. Establish `e : c (loc v s) - (ρ (loc v s) (P v (x v)) - P v (x v)) = (c (loc v s) - (ρ (loc v s) (x v) - x v)) - (ρ (loc v s) (P v (x v) - x v) - (P v (x v) - x v))`. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws. Simplify using `only at h1 ⊢`.

Rewrite using `[e]`. Conclude with `(b v).sub_mem h1 h2`. Simplify using `[Submodule.mem_pi, hPn]`. Use `⟨⟨_, hmem⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [q, LinearMap.comp_apply, Submodule.mkQ_apply]`.

Rewrite using `[Submodule.Quotient.eq]`. Use `⟨0, fun s => ?_, fun v => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `using hPb v (x v)`. Establish `fmem : ∀ X : W, ((fun s => ρ s X - X, fun v => P v X) : (G → W) × (V → W)) ∈ S`.

Introduce `X`. Use `⟨⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(hlc X).sub (IsLocallyConstant.const X)`. Introduce `s u`. Simplify using `only [map_mul, Module.End.mul_apply, map_sub]`.

Normalize the expressions using the abelian group laws. Introduce `v s`. Establish `h2` using `hloc v s _ (hPb' v X)`. Establish `e : (ρ (loc v s) X - X) - (ρ (loc v s) (P v X) - P v X) = ρ (loc v s) (X - P v X) - (X - P v X)`. Rewrite using `[map_sub]`.

Normalize the expressions using the abelian group laws. Simplify using `only`. Rewrite using `[e]`. Conclude with `h2`. Simplify using `[Submodule.mem_pi, hPn]`.

Set `f : W →ₗ[k] S` to `{ toFun := fun X => ⟨_, fmem X⟩ map_add' := fun X Y => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply the tactic sequence `ext s <;> simp <;> abel`. Use the proof step `map_smul' := fun a X => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply the tactic sequence `ext s <;> simp [smul_sub] }`. Establish `hf : ∀ X, q (f X) = 0`. Introduce `X`. Simplify using `only [q, LinearMap.comp_apply, Submodule.mkQ_apply]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Conclude with `⟨X, fun s => rfl, fun v => hPb v X⟩`. Establish `h0 : LinearMap.ker f ≤ Fr.coneH0 ρ b`. Introduce `X hX`. Rewrite `hX` using `[LinearMap.mem_ker]`. Establish `h1` using `congrArg (fun z : S => z.1.1) hX`.

Establish `h2` using `congrArg (fun z : S => z.1.2) hX`. Use `⟨fun g => ?_, fun v => ?_⟩` and prove the remaining obligations. Use `congrFun h1 g` as an intermediate fact. Simplify using `[f] at this`. Conclude with `sub_eq_zero.mp this`.

Use `congrFun h2 v` as an intermediate fact. Establish `hb` using `hPb v X`. Simplify using `[f] at this`. Rewrite `hb` using `[this, zero_sub]`. Simplify using `using (b v).neg_mem hb`.

Set `e : S →ₗ[k] W ⧸ t` to `t.mkQ ∘ₗ (LinearMap.proj g0 ∘ₗ LinearMap.fst k (G → W) (V → W)) ∘ₗ S.subtype`. Establish `jmem : ∀ z : LinearMap.ker e, (z.1.1 : (G → W) × (V → W)) ∈ TanC loc ρ b n g0 t`. Introduce and unpack `⟨⟨z, hz1, hz2⟩, hze⟩`. Rewrite `hze` using `[LinearMap.mem_ker]`. Use `⟨hz1, ?_, ?_⟩` and prove the remaining obligations.

Simplify `hze` using `[e, Submodule.Quotient.mk_eq_zero]`. Conclude with `hz2`. Set `j : LinearMap.ker e →ₗ[k] TanC loc ρ b n g0 t` to `LinearMap.codRestrict _ (S.subtype ∘ₗ (LinearMap.ker e).subtype) jmem`. Establish `hj : Function.Injective j`. Introduce `z z' h`.

Use `congrArg Subtype.val h` as an intermediate fact. Conclude with `Subtype.ext (Subtype.ext this)`. Use `haveI : Module.Finite k (TanC loc ρ b n g0 t) := hfin`. Conclude with `dimLem t (Fr.coneH0 ρ b) e j hj q hq f hf h0`.
-/
theorem UpperTheory.V.Ws.X1.coneTan :
    ∀ {k G W V : Type} [Field k] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module k W] [Module.Finite k W] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G) (ρ : Representation k G W) (b n : V → Submodule k W) (g0 : G) (t : Submodule k W), (∀ X, IsLocallyConstant fun g => ρ g X) → (∀ v s, ∀ X ∈ b v, ρ (loc v s) X ∈ b v) → (∀ v, IsCompl (b v) (n v)) → Module.Finite k (TanC loc ρ b n g0 t) → Module.finrank k (Fr.H1C loc ρ b) + Module.finrank k t ≤ Module.finrank k (TanC loc ρ b n g0 t) + Module.finrank k (Fr.coneH0 ρ b) := by
  intro k G W V _ _ _ _ _ _ Gv _ loc ρ b n g0 t hlc hstab hcompl hfin
  choose P hPn hPb using fun v => exProj (b v) (n v) (hcompl v)
  have hPb' : ∀ v x, x - P v x ∈ b v := fun v x => by
    simpa using (b v).neg_mem (hPb v x)
  have hloc : ∀ v (s : Gv v) (y : W), y ∈ b v → ρ (loc v s) y - y ∈ b v := fun v s y hy =>
    (b v).sub_mem (hstab v s y hy) hy
  set S : Submodule k ((G → W) × (V → W)) :=
    Fr.Z1C loc ρ b ⊓ Submodule.comap (LinearMap.snd k (G → W) (V → W)) (Submodule.pi Set.univ n) with hSd
  let q : S →ₗ[k] Fr.H1C loc ρ b :=
    (Submodule.mkQ _) ∘ₗ Submodule.inclusion (inf_le_left : S ≤ Fr.Z1C loc ρ b)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨⟨c, x⟩, hz⟩ := z
    obtain ⟨hz1, hz2, hz3⟩ := hz
    have hmem : ((c, fun v => P v (x v)) : (G → W) × (V → W)) ∈ S := by
      refine ⟨⟨hz1, hz2, fun v s => ?_⟩, ?_⟩
      · have h1 := hz3 v s
        have h2 := hloc v s _ (hPb v (x v))
        have e : c (loc v s) - (ρ (loc v s) (P v (x v)) - P v (x v)) =
            (c (loc v s) - (ρ (loc v s) (x v) - x v)) -
              (ρ (loc v s) (P v (x v) - x v) - (P v (x v) - x v)) := by
          rw [map_sub]; abel
        simp only at h1 ⊢
        rw [e]
        exact (b v).sub_mem h1 h2
      · simp [Submodule.mem_pi, hPn]
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only [q, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    refine ⟨0, fun s => ?_, fun v => ?_⟩
    · simp
    · simpa using hPb v (x v)
  have fmem : ∀ X : W, ((fun s => ρ s X - X, fun v => P v X) : (G → W) × (V → W)) ∈ S := by
    intro X
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact (hlc X).sub (IsLocallyConstant.const X)
    · intro s u
      simp only [map_mul, Module.End.mul_apply, map_sub]
      abel
    · intro v s
      have h2 := hloc v s _ (hPb' v X)
      have e : (ρ (loc v s) X - X) - (ρ (loc v s) (P v X) - P v X) =
          ρ (loc v s) (X - P v X) - (X - P v X) := by
        rw [map_sub]; abel
      simp only
      rw [e]
      exact h2
    · simp [Submodule.mem_pi, hPn]
  let f : W →ₗ[k] S :=
    { toFun := fun X => ⟨_, fmem X⟩
      map_add' := fun X Y => by
        apply Subtype.ext
        ext s <;> simp <;> abel
      map_smul' := fun a X => by
        apply Subtype.ext
        ext s <;> simp [smul_sub] }
  have hf : ∀ X, q (f X) = 0 := by
    intro X
    simp only [q, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨X, fun s => rfl, fun v => hPb v X⟩
  have h0 : LinearMap.ker f ≤ Fr.coneH0 ρ b := by
    intro X hX
    rw [LinearMap.mem_ker] at hX
    have h1 := congrArg (fun z : S => z.1.1) hX
    have h2 := congrArg (fun z : S => z.1.2) hX
    refine ⟨fun g => ?_, fun v => ?_⟩
    · have := congrFun h1 g
      simp [f] at this
      exact sub_eq_zero.mp this
    · have := congrFun h2 v
      have hb := hPb v X
      simp [f] at this
      rw [this, zero_sub] at hb
      simpa using (b v).neg_mem hb
  let e : S →ₗ[k] W ⧸ t :=
    t.mkQ ∘ₗ (LinearMap.proj g0 ∘ₗ LinearMap.fst k (G → W) (V → W)) ∘ₗ S.subtype
  have jmem : ∀ z : LinearMap.ker e, (z.1.1 : (G → W) × (V → W)) ∈ TanC loc ρ b n g0 t := by
    rintro ⟨⟨z, hz1, hz2⟩, hze⟩
    rw [LinearMap.mem_ker] at hze
    refine ⟨hz1, ?_, ?_⟩
    · simpa [e, Submodule.Quotient.mk_eq_zero] using hze
    · exact hz2
  let j : LinearMap.ker e →ₗ[k] TanC loc ρ b n g0 t :=
    LinearMap.codRestrict _ (S.subtype ∘ₗ (LinearMap.ker e).subtype) jmem
  have hj : Function.Injective j := by
    intro z z' h
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  haveI : Module.Finite k (TanC loc ρ b n g0 t) := hfin
  exact dimLem t (Fr.coneH0 ρ b) e j hj q hq f hf h0
