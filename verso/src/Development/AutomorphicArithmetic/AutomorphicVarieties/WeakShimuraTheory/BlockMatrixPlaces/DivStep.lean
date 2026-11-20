import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

/- English proof (translation)
Establish `hm : maximalIdeal A = Ideal.span {t}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht`. Use `show x ∈ maximalIdeal A ^ n • (⊤ : Submodule A T) ↔ _`. Rewrite using `[hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Simplify using the standard rewrite rules.
-/
private theorem mem_lev_iff {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {T : Type} [AddCommGroup T]
    [Module A T] {t : A} (ht : Irreducible t) (n : ℕ) (x : T) : x ∈ lev A T n ↔ ∃ w, t ^ n • w = x := by
  have hm : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht
  show x ∈ maximalIdeal A ^ n • (⊤ : Submodule A T) ↔ _
  rw [hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

/- English proof (translation)
Set `g` to `Q.mapQ Q f hQ`. Establish `hs : Function.Surjective g`. Introduce `q`. Take `⟨x, rfl⟩` from `Q.mkQ_surjective q`. Take `⟨w, rfl⟩` from `hf x`.

Conclude with `⟨Q.mkQ w, by simp [g]⟩`. Establish `hi` using `OrzechProperty.injective_of_surjective_endomorphism g hs`. Establish `h0 : g (Q.mkQ y) = g 0`. Simplify using `only [g, Submodule.mkQ_apply, Submodule.mapQ_apply, map_zero]`. Conclude with `(Submodule.Quotient.mk_eq_zero Q).2 hy`.

Establish `h1` using `hi h0`. Simplify using `using h1`.
-/
private theorem mem_of_bij {A : Type} [CommRing A] {T : Type} [AddCommGroup T] [Module A T] [Module.Finite A T]
    (f : T →ₗ[A] T) (hf : Function.Surjective f) (Q : Submodule A T) (hQ : Q ≤ Q.comap f) {y : T} (hy : f y ∈ Q) :
    y ∈ Q := by
  let g := Q.mapQ Q f hQ
  have hs : Function.Surjective g := by
    intro q
    obtain ⟨x, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨w, rfl⟩ := hf x
    exact ⟨Q.mkQ w, by simp [g]⟩
  have hi := OrzechProperty.injective_of_surjective_endomorphism g hs
  have h0 : g (Q.mkQ y) = g 0 := by
    simp only [g, Submodule.mkQ_apply, Submodule.mapQ_apply, map_zero]
    exact (Submodule.Quotient.mk_eq_zero Q).2 hy
  have h1 := hi h0
  simpa using h1

/- English proof (translation)
Introduce `A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL t ht n z hz hnp`. Take `⟨y, hzy⟩` from `hz`. Establish `ht0 : t ≠ 0` using `ht.ne_zero`. Establish `hinjt : Function.Injective (fun x : T => t • x)` using `smul_right_injective T ht0`. Establish `hlev` using `fun k x => mem_lev_iff (T := T) ht k x`.

Establish `hφ : lev A T n ≤ (lev A T (n + 1)).comap (t • LinearMap.id)`. Introduce `x hx`. Take `⟨w, rfl⟩` from `(hlev n x).1 hx`. Rewrite using `[Submodule.mem_comap]`. Use `(hlev (n + 1) _).2 ⟨w, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.smul_apply, LinearMap.id_apply, pow_succ', mul_smul]`. Set `φ` to `(lev A T n).mapQ (lev A T (n + 1)) (t • LinearMap.id) hφ`. Establish `hφmk : ∀ x, φ ((lev A T n).mkQ x) = (lev A T (n + 1)).mkQ (t • x)` using `fun x => rfl`. Establish `hφinj : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `a ha`. Take `⟨x, rfl⟩` from `(lev A T n).mkQ_surjective a`. Rewrite `ha` using `[hφmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨w, hw⟩` from `(hlev (n + 1) _).1 ha`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Use `(hlev n x).2 ⟨w, hinjt ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← hw, pow_succ', mul_smul]`. Establish `hφP : ∀ a, φ a ∈ Submodule.map (lev A T (n + 1)).mkQ P → a ∈ Submodule.map (lev A T n).mkQ P`. Introduce `a ha`.

Take `⟨x, rfl⟩` from `(lev A T n).mkQ_surjective a`. Take `⟨q, hq, hqe⟩` from `Submodule.mem_map.1 ha`. Rewrite `hqe` using `[hφmk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Take `⟨v, hv⟩` from `(hlev (n + 1) _).1 hqe`. Establish `hq' : t • (x + t ^ n • v) ∈ P`.

Establish `e : t • (x + t ^ n • v) = q`. Rewrite using `[smul_add, ← mul_smul, ← pow_succ', hv]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `hq`.

Establish `hxP` using `hL.sat t _ ht0 hq'`. Use `Submodule.mem_map.2 ⟨x + t ^ n • v, hxP, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Conclude with `(hlev n _).2 ⟨v, by abel⟩`. Establish `hφρ : ∀ g a, φ (modRep ρ n g a) = modRep ρ (n + 1) g (φ a)`.

Introduce `g a`. Take `⟨x, rfl⟩` from `(lev A T n).mkQ_surjective a`. Rewrite using `[modRep_mk, hφmk, hφmk, modRep_mk, LinearMap.map_smul (ρ g) t x]`. Establish `hz1 : ∀ g, z g ∈ Submodule.map (lev A T (n + 1)).mkQ (lev A T 1)`. Introduce `g`.

Assume the negation of the conclusion as `hc`. Conclude with `hnp ⟨g, hc⟩`. Establish `hrange : ∀ g, ∃ a, φ a = z g`. Introduce `g`. Take `⟨u, hu, hue⟩` from `Submodule.mem_map.1 (hz1 g)`.

Take `⟨w, rfl⟩` from `(hlev 1 u).1 hu`. Use `⟨(lev A T n).mkQ w, ?_⟩` and prove the remaining obligations. Rewrite using `[hφmk, ← hue, pow_one]`. Use `choose z' hz' using hrange`. Take `⟨s, hsH, hsb⟩` from `hL.fr`.

Take `⟨y0, rfl⟩` from `(lev A T (n + 1)).mkQ_surjective y`. Establish `hle1 : lev A T (n + 1) ≤ lev A T 1` using `Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))`. Establish `hy0 : y0 ∈ P ⊔ lev A T 1`. Set `f : T →ₗ[A] T` to `ρ s - LinearMap.id`. Establish `hfs : Function.Surjective f` using `hsb.2`.

Apply `mem_of_bij f hfs` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[Submodule.mem_comap]`. Use `show ρ s x - x ∈ _`. Apply `Submodule.sub_mem _ _ hx` to reduce the goal to its premises.

Take `⟨p, hp, q, hq, rfl⟩` from `Submodule.mem_sup.1 hx`. Use `Submodule.mem_sup.2 ⟨ρ s p, hL.stab s hsH p hp, ρ s q, ?_, (map_add _ _ _).symm⟩` and prove the remaining obligations. Take `⟨w, rfl⟩` from `(hlev 1 q).1 hq`. Conclude with `(hlev 1 _).2 ⟨ρ s w, (map_smul _ _ _).symm⟩`. Use `show ρ s y0 - y0 ∈ _`.

Establish `hloc : z s - (modRep ρ (n + 1) s ((lev A T (n + 1)).mkQ y0) - (lev A T (n + 1)).mkQ y0) ∈ Submodule.map (lev A T (n + 1)).mkQ P` using `hzy.loc s hsH`. Take `⟨p, hp, hpe⟩` from `Submodule.mem_map.1 hloc`. Take `⟨u, hu, hue⟩` from `Submodule.mem_map.1 (hz1 s)`. Rewrite `hpe` using `[modRep_mk, ← hue, ← map_sub, ← map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Establish `e : ρ s y0 - y0 = ((p - (u - (ρ s y0 - y0))) + u) - p` using `by abel`.

Rewrite using `[e]`. Apply `Submodule.sub_mem _ _ (Submodule.mem_sup_left hp)` to reduce the goal to its premises. Apply `Submodule.add_mem _ (Submodule.mem_sup_right (hle1 hpe)) (Submodule.mem_sup_right hu)` to reduce the goal to its premises. Take `⟨p0, hp0, q0, hq0, hpq⟩` from `Submodule.mem_sup.1 hy0`. Take `⟨w0, rfl⟩` from `(hlev 1 q0).1 hq0`.

Substitute `hpq` using the available equality. Establish `hcomp : ⇑φ ∘ z' = z` using `funext hz'`. Use `⟨z', ⟨(lev A T n).mkQ w0, ?_⟩, ?_⟩` and prove the remaining obligations. Use `⟨IsLocallyConstant.desc z' φ (by rw [hcomp]; exact hzy.lc) hφinj, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g h show z' (g * h) = z' g + modRep ρ n g (z' h)`.

Apply `hφinj` to reduce the goal to its premises. Rewrite using `[hz', map_add, hφρ, hz', hz']`. Conclude with `hzy.coc g h`. Apply `hφinj` to reduce the goal to its premises. Rewrite using `[hz', map_zero]`.

Conclude with `hzy.cz`. Introduce `g hg`. Apply `hφinj` to reduce the goal to its premises. Rewrite using `[hz', map_zero]`. Conclude with `hzy.kill g hg`.

Introduce `h hh show z' h - (modRep ρ n h ((lev A T n).mkQ w0) - (lev A T n).mkQ w0) ∈ Submodule.map (lev A T n).mkQ P`. Apply `hφP` to reduce the goal to its premises. Rewrite using `[map_sub, map_sub, hφρ, hz', hφmk]`. Establish `hloc : z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0)) - (lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0)) ∈ Submodule.map (lev A T (n + 1)).mkQ P` using `hzy.loc h hh`. Establish `e : z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (t • w0)) - (lev A T (n + 1)).mkQ (t • w0)) = (z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0)) - (lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))) + (lev A T (n + 1)).mkQ (ρ h p0 - p0)`.

Simplify using `only [pow_one, map_add, map_sub, modRep_mk]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Submodule.add_mem _ hloc (Submodule.mem_map_of_mem (Submodule.sub_mem _ (hL.stab h hh p0 hp0) hp0))`. Introduce `g x hx`.

Rewrite using `[← hφmk, hx, hz']`.
-/
theorem UpperTheory.V.Ws.Bl.divStep :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), Lat ρ H P → ∀ t : A, Irreducible t → ∀ n, ∀ z ∈ Zn ρ c N H P (n + 1), ¬ Prim z →
          ∃ z' ∈ Zn ρ c N H P n, ∀ g x, (lev A T n).mkQ x = z' g → (lev A T (n + 1)).mkQ (t • x) = z g := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL t ht n z hz hnp
  obtain ⟨y, hzy⟩ := hz
  have ht0 : t ≠ 0 := ht.ne_zero
  have hinjt : Function.Injective (fun x : T => t • x) := smul_right_injective T ht0
  have hlev := fun k x => mem_lev_iff (T := T) ht k x
  have hφ : lev A T n ≤ (lev A T (n + 1)).comap (t • LinearMap.id) := by
    intro x hx
    obtain ⟨w, rfl⟩ := (hlev n x).1 hx
    rw [Submodule.mem_comap]
    refine (hlev (n + 1) _).2 ⟨w, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, pow_succ', mul_smul]
  let φ := (lev A T n).mapQ (lev A T (n + 1)) (t • LinearMap.id) hφ
  have hφmk : ∀ x, φ ((lev A T n).mkQ x) = (lev A T (n + 1)).mkQ (t • x) := fun x => rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    rw [hφmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at ha
    obtain ⟨w, hw⟩ := (hlev (n + 1) _).1 ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine (hlev n x).2 ⟨w, hinjt ?_⟩
    simp only
    rw [← hw, pow_succ', mul_smul]
  have hφP : ∀ a, φ a ∈ Submodule.map (lev A T (n + 1)).mkQ P →
      a ∈ Submodule.map (lev A T n).mkQ P := by
    intro a ha
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    obtain ⟨q, hq, hqe⟩ := Submodule.mem_map.1 ha
    rw [hφmk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hqe
    obtain ⟨v, hv⟩ := (hlev (n + 1) _).1 hqe
    have hq' : t • (x + t ^ n • v) ∈ P := by
      have e : t • (x + t ^ n • v) = q := by
        rw [smul_add, ← mul_smul, ← pow_succ', hv]
        abel
      rw [e]
      exact hq
    have hxP := hL.sat t _ ht0 hq'
    refine Submodule.mem_map.2 ⟨x + t ^ n • v, hxP, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact (hlev n _).2 ⟨v, by abel⟩
  have hφρ : ∀ g a, φ (modRep ρ n g a) = modRep ρ (n + 1) g (φ a) := by
    intro g a
    obtain ⟨x, rfl⟩ := (lev A T n).mkQ_surjective a
    rw [modRep_mk, hφmk, hφmk, modRep_mk, LinearMap.map_smul (ρ g) t x]
  have hz1 : ∀ g, z g ∈ Submodule.map (lev A T (n + 1)).mkQ (lev A T 1) := by
    intro g
    by_contra hc
    exact hnp ⟨g, hc⟩
  have hrange : ∀ g, ∃ a, φ a = z g := by
    intro g
    obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 (hz1 g)
    obtain ⟨w, rfl⟩ := (hlev 1 u).1 hu
    refine ⟨(lev A T n).mkQ w, ?_⟩
    rw [hφmk, ← hue, pow_one]
  choose z' hz' using hrange
  obtain ⟨s, hsH, hsb⟩ := hL.fr
  obtain ⟨y0, rfl⟩ := (lev A T (n + 1)).mkQ_surjective y
  have hle1 : lev A T (n + 1) ≤ lev A T 1 :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
  have hy0 : y0 ∈ P ⊔ lev A T 1 := by
    let f : T →ₗ[A] T := ρ s - LinearMap.id
    have hfs : Function.Surjective f := hsb.2
    apply mem_of_bij f hfs
    · intro x hx
      rw [Submodule.mem_comap]
      show ρ s x - x ∈ _
      apply Submodule.sub_mem _ _ hx
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
      refine Submodule.mem_sup.2 ⟨ρ s p, hL.stab s hsH p hp, ρ s q, ?_, (map_add _ _ _).symm⟩
      obtain ⟨w, rfl⟩ := (hlev 1 q).1 hq
      exact (hlev 1 _).2 ⟨ρ s w, (map_smul _ _ _).symm⟩
    · show ρ s y0 - y0 ∈ _
      have hloc : z s - (modRep ρ (n + 1) s ((lev A T (n + 1)).mkQ y0) - (lev A T (n + 1)).mkQ y0)
          ∈ Submodule.map (lev A T (n + 1)).mkQ P := hzy.loc s hsH
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hloc
      obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 (hz1 s)
      rw [modRep_mk, ← hue, ← map_sub, ← map_sub, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq] at hpe
      have e : ρ s y0 - y0 = ((p - (u - (ρ s y0 - y0))) + u) - p := by abel
      rw [e]
      apply Submodule.sub_mem _ _ (Submodule.mem_sup_left hp)
      apply Submodule.add_mem _ (Submodule.mem_sup_right (hle1 hpe)) (Submodule.mem_sup_right hu)
  obtain ⟨p0, hp0, q0, hq0, hpq⟩ := Submodule.mem_sup.1 hy0
  obtain ⟨w0, rfl⟩ := (hlev 1 q0).1 hq0
  subst hpq
  have hcomp : ⇑φ ∘ z' = z := funext hz'
  refine ⟨z', ⟨(lev A T n).mkQ w0, ?_⟩, ?_⟩
  · refine ⟨IsLocallyConstant.desc z' φ (by rw [hcomp]; exact hzy.lc) hφinj, ?_, ?_, ?_, ?_⟩
    · intro g h
      show z' (g * h) = z' g + modRep ρ n g (z' h)
      apply hφinj
      rw [hz', map_add, hφρ, hz', hz']
      exact hzy.coc g h
    · apply hφinj
      rw [hz', map_zero]
      exact hzy.cz
    · intro g hg
      apply hφinj
      rw [hz', map_zero]
      exact hzy.kill g hg
    · intro h hh
      show z' h - (modRep ρ n h ((lev A T n).mkQ w0) - (lev A T n).mkQ w0)
        ∈ Submodule.map (lev A T n).mkQ P
      apply hφP
      rw [map_sub, map_sub, hφρ, hz', hφmk]
      have hloc : z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))
          - (lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0)) ∈ Submodule.map (lev A T (n + 1)).mkQ P :=
        hzy.loc h hh
      have e : z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (t • w0)) - (lev A T (n + 1)).mkQ (t • w0))
          = (z h - (modRep ρ (n + 1) h ((lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))
            - (lev A T (n + 1)).mkQ (p0 + t ^ 1 • w0))) + (lev A T (n + 1)).mkQ (ρ h p0 - p0) := by
        simp only [pow_one, map_add, map_sub, modRep_mk]
        abel
      rw [e]
      exact Submodule.add_mem _ hloc
        (Submodule.mem_map_of_mem (Submodule.sub_mem _ (hL.stab h hh p0 hp0) hp0))
  · intro g x hx
    rw [← hφmk, hx, hz']
