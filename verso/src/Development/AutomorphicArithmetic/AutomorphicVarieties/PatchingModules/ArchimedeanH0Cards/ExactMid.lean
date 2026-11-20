import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.PushforwardPreservesSelmerCocycles

open ReciprocityTheory.Gal UpperTheory.V.Pa UpperTheory.V.Pa.B2

section SlopeTestRemainingChoices

variable {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ}

/- English proof (translation)
Take `⟨x, hx, h1, h2⟩` from `hb`. Establish `hc : ∀ s t : Γ, b.1 (s, t) = D.M.ρ s (x t) - x (s * t) + x s`. Introduce `s t`. Rewrite using `[h1]`. Conclude with `d1_apply _ _ _ _`.

Use `⟨⟨?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `e : b.1 = fun q : Γ × Γ => D.M.ρ q.1 (x q.2) - x (q.1 * q.2) + x q.1`. Use function extensionality and compare the values at `q`. Conclude with `hc q.1 q.2`. Rewrite using `[e]`.

Establish `hact : Continuous fun p : Γ × D.M.X => D.M.ρ p.1 p.2` using `D.M.cont`. Establish `h3 : Continuous fun q : Γ × Γ => D.M.ρ q.1 (x q.2)` using `hact.comp (continuous_fst.prodMk (hx.comp continuous_snd))`. Conclude with `(h3.sub (hx.comp continuous_mul)).add (hx.comp continuous_fst)`. Introduce `g h k`. Rewrite using `[hc, hc, hc, hc]`.

Simplify using `only [map_sub, map_add, map_mul, Module.End.mul_apply, mul_assoc]`. Normalize the expressions using the abelian group laws. Establish `hF : Continuous fun g : P.G w => D.π w (x (P.φ w g))` using `(continuous_of_discreteTopology (f := D.π w)).comp (hx.comp (P.cont w))`. Establish `hy` using `(h2 w).1.1`. Use `hy.add hF` as an intermediate fact.

Simplify using `using this`. Introduce `g h`. Establish `hyg` using `(h2 w).1.2 g h`. Simplify using `only [Pi.sub_apply, map_sub] at hyg`. Establish `e : b.2 w (g * h) = b.2 w g - D.π w (x (P.φ w g)) + ((D.Q w).ρ g (b.2 w h) - (D.Q w).ρ g (D.π w (x (P.φ w h)))) + D.π w (x (P.φ w (g * h)))`.

Rewrite `hyg`, the goal using `[← sub_eq_zero]`. Rewrite using `[← hyg]`. Normalize the expressions using the abelian group laws. Rewrite using `[hc, d1_apply, e, ← (P.φ w).map_mul g h]`. Simplify using `only [map_sub, map_add, D.equiv]`.

Normalize the expressions using the abelian group laws.
-/
private theorem coboundary_mem_cocycles_local [IsTopologicalGroup Γ] (D : Dat A P) {b : D.C2} (hb : b ∈ D.selmerSecondCoboundaries) : b ∈ D.selmerSecondCocycles := by
  obtain ⟨x, hx, h1, h2⟩ := hb
  have hc : ∀ s t : Γ, b.1 (s, t) = D.M.ρ s (x t) - x (s * t) + x s := by
    intro s t
    rw [h1]
    exact d1_apply _ _ _ _
  refine ⟨⟨?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩
  · have e : b.1 = fun q : Γ × Γ => D.M.ρ q.1 (x q.2) - x (q.1 * q.2) + x q.1 := by
      funext q
      exact hc q.1 q.2
    rw [e]
    have hact : Continuous fun p : Γ × D.M.X => D.M.ρ p.1 p.2 := D.M.cont
    have h3 : Continuous fun q : Γ × Γ => D.M.ρ q.1 (x q.2) :=
      hact.comp (continuous_fst.prodMk (hx.comp continuous_snd))
    exact (h3.sub (hx.comp continuous_mul)).add (hx.comp continuous_fst)
  · intro g h k
    rw [hc, hc, hc, hc]
    simp only [map_sub, map_add, map_mul, Module.End.mul_apply, mul_assoc]
    abel
  · have hF : Continuous fun g : P.G w => D.π w (x (P.φ w g)) :=
      (continuous_of_discreteTopology (f := D.π w)).comp (hx.comp (P.cont w))
    have hy := (h2 w).1.1
    have := hy.add hF
    simpa using this
  · intro g h
    have hyg := (h2 w).1.2 g h
    simp only [Pi.sub_apply, map_sub] at hyg
    have e : b.2 w (g * h) = b.2 w g - D.π w (x (P.φ w g)) + ((D.Q w).ρ g (b.2 w h)
        - (D.Q w).ρ g (D.π w (x (P.φ w h)))) + D.π w (x (P.φ w (g * h))) := by
      rw [← sub_eq_zero] at hyg ⊢
      rw [← hyg]
      abel
    rw [hc, d1_apply, e, ← (P.φ w).map_mul g h]
    simp only [map_sub, map_add, D.equiv]
    abel

/- English proof (translation)
Take `⟨x'', hx'', h1, h2⟩` from `hq`. Use `choose s hs' using hs`. Establish `hl'` using `fun w => hl w _ (h2 w)`. Use `choose y hyL hy using hl'`. Establish `hx : Continuous fun t : Γ => s (x'' t)` using `(continuous_of_discreteTopology (f := s)).comp hx''`.

Use `⟨(d1 D.M.ρ (fun t => s (x'' t)), fun w h => D.π w (s (x'' (P.φ w h))) + y w h), ⟨fun t => s (x'' t), hx, rfl, fun w => ?_⟩, ?_⟩` and prove the remaining obligations. Use `hyL w using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `h`. Simplify using the standard rewrite rules. Use `Prod.ext (funext fun st => ?_) (funext fun w => funext fun h => ?_)` and prove the remaining obligations.

Take `⟨a, c⟩` from `st show g.f (d1 D.M.ρ (fun t => s (x'' t)) (a, c)) = q.1 (a, c)`. Rewrite using `[h1, d1_apply, d1_apply]`. Simplify using `only [map_sub, map_add, g.equiv, hs']`. Use `show g.fq w (D.π w (s (x'' (P.φ w h))) + y w h) = q.2 w h`. Rewrite using `[map_add, g.comm, hs', hy w h]`.

Simplify using the standard rewrite rules.
-/
private theorem coboundary_lift_local_conditions {D D'' : Dat A P} (g : D.Hom D'') (hs : Function.Surjective g.f)
    (hl : ∀ w, ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s)
    {q : D''.C2} (hq : q ∈ D''.selmerSecondCoboundaries) : ∃ b ∈ D.selmerSecondCoboundaries, g.c2 b = q := by
  obtain ⟨x'', hx'', h1, h2⟩ := hq
  choose s hs' using hs
  have hl' := fun w => hl w _ (h2 w)
  choose y hyL hy using hl'
  have hx : Continuous fun t : Γ => s (x'' t) :=
    (continuous_of_discreteTopology (f := s)).comp hx''
  refine ⟨(d1 D.M.ρ (fun t => s (x'' t)), fun w h => D.π w (s (x'' (P.φ w h))) + y w h),
    ⟨fun t => s (x'' t), hx, rfl, fun w => ?_⟩, ?_⟩
  · convert hyL w using 1
    funext h
    simp
  · refine Prod.ext (funext fun st => ?_) (funext fun w => funext fun h => ?_)
    · obtain ⟨a, c⟩ := st
      show g.f (d1 D.M.ρ (fun t => s (x'' t)) (a, c)) = q.1 (a, c)
      rw [h1, d1_apply, d1_apply]
      simp only [map_sub, map_add, g.equiv, hs']
    · show g.fq w (D.π w (s (x'' (P.φ w h))) + y w h) = q.2 w h
      rw [map_add, g.comm, hs', hy w h]
      simp

/- English proof (translation)
Establish `e1 : ∀ st, g.f (p.1 st) = 0` using `fun st => congrFun (congrArg Prod.fst h0) st`. Establish `e2 : ∀ w t, g.fq w (p.2 w t) = 0` using `fun w t => congrFun (congrFun (congrArg Prod.snd h0) w) t`. Use `choose a ha using fun st => (h.ex (p.1 st)).1 (e1 st)`. Use `choose c hc using fun w t => (h.exq w (p.2 w t)).1 (e2 w t)`. Take `⟨⟨hpc, hpcoc⟩, hpw⟩` from `hp`.

Use `⟨(a, c), ⟨⟨?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩, Prod.ext (funext ha) (funext fun w => funext (hc w))⟩` and prove the remaining obligations. Establish `ea : a = fun st => Function.invFun f.f (p.1 st)` using `funext fun st => h.inj (by rw [ha]; exact (Function.invFun_eq ⟨a st, ha st⟩).symm) show Continuous a`. Rewrite using `[ea]`. Conclude with `(continuous_of_discreteTopology (f := Function.invFun f.f)).comp hpc`. Introduce `u v k`.

Apply `h.inj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Simplify using `only [map_sub, map_add, f.equiv, ha]`. Conclude with `hpcoc u v k`. Establish `ec : c w = fun t => Function.invFun (f.fq w) (p.2 w t)` using `funext fun t => h.injq w (by rw [hc]; exact (Function.invFun_eq ⟨c w t, hc w t⟩).symm) show Continuous (c w)`.

Rewrite using `[ec]`. Conclude with `(continuous_of_discreteTopology (f := Function.invFun (f.fq w))).comp (hpw w).1`. Introduce `u v`. Apply `h.injq w` to reduce the goal to its premises. Rewrite using `[f.comm, ha, (hpw w).2 u v, d1_apply, d1_apply]`.

Simplify using `only [map_sub, map_add, f.equivq, hc]`.
-/
private theorem cocycle_descends_short_exact {D' D D'' : Dat A P} (f : D'.Hom D) (g : D.Hom D'') (h : Dat.SES f g)
    {p : D.C2} (hp : p ∈ D.selmerSecondCocycles) (h0 : g.c2 p = 0) : ∃ p' ∈ D'.selmerSecondCocycles, f.c2 p' = p := by
  have e1 : ∀ st, g.f (p.1 st) = 0 := fun st => congrFun (congrArg Prod.fst h0) st
  have e2 : ∀ w t, g.fq w (p.2 w t) = 0 := fun w t =>
    congrFun (congrFun (congrArg Prod.snd h0) w) t
  choose a ha using fun st => (h.ex (p.1 st)).1 (e1 st)
  choose c hc using fun w t => (h.exq w (p.2 w t)).1 (e2 w t)
  obtain ⟨⟨hpc, hpcoc⟩, hpw⟩ := hp
  refine ⟨(a, c), ⟨⟨?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩,
    Prod.ext (funext ha) (funext fun w => funext (hc w))⟩
  · have ea : a = fun st => Function.invFun f.f (p.1 st) := funext fun st =>
      h.inj (by rw [ha]; exact (Function.invFun_eq ⟨a st, ha st⟩).symm)
    show Continuous a
    rw [ea]
    exact (continuous_of_discreteTopology (f := Function.invFun f.f)).comp hpc
  · intro u v k
    apply h.inj
    rw [map_zero]
    simp only [map_sub, map_add, f.equiv, ha]
    exact hpcoc u v k
  · have ec : c w = fun t => Function.invFun (f.fq w) (p.2 w t) := funext fun t =>
      h.injq w (by rw [hc]; exact (Function.invFun_eq ⟨c w t, hc w t⟩).symm)
    show Continuous (c w)
    rw [ec]
    exact (continuous_of_discreteTopology (f := Function.invFun (f.fq w))).comp (hpw w).1
  · intro u v
    apply h.injq w
    rw [f.comm, ha, (hpw w).2 u v, d1_apply, d1_apply]
    simp only [map_sub, map_add, f.equivq, hc]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `A Γ _ _ _ _ P D' D D'' f g h hl z hz`. Take `⟨p, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Rewrite `hz` using `[LinearMap.mem_ker, Dat.Hom.h2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Establish `hq : g.c2 p.1 ∈ D''.selmerSecondCoboundaries` using `hz`. Take `⟨b, hb, hbq⟩` from `coboundary_lift_local_conditions g h.surj hl hq`.

Establish `hm : p.1 - b ∈ D.selmerSecondCocycles` using `sub_mem p.2 (coboundary_mem_cocycles_local D hb)`. Establish `h0 : g.c2 (p.1 - b) = 0` using `by rw [map_sub, hbq, sub_self]`. Take `⟨p', hp', hfp⟩` from `cocycle_descends_short_exact f g h hm h0`. Rewrite using `[LinearMap.mem_range]`. Use `⟨Submodule.Quotient.mk ⟨p', hp'⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Dat.Hom.h2, Submodule.mapQ_apply, Submodule.Quotient.eq]`. Use `show f.c2 p' - p.1 ∈ D.selmerSecondCoboundaries`. Rewrite using `[hfp, sub_sub_cancel_left]`. Conclude with `neg_mem hb`.
-/
theorem UpperTheory.V.Pa.B2.exactMid :
    ∀ (A Γ : Type) [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (P : Pl Γ) (D' D D'' : Dat A P) (f : D'.Hom D) (g : D.Hom D''), Dat.SES f g → (∀ w, ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s) → LinearMap.ker g.h2 ≤ LinearMap.range f.h2 := by
  intro A Γ _ _ _ _ P D' D D'' f g h hl z hz
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker, Dat.Hom.h2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  have hq : g.c2 p.1 ∈ D''.selmerSecondCoboundaries := hz
  obtain ⟨b, hb, hbq⟩ := coboundary_lift_local_conditions g h.surj hl hq
  have hm : p.1 - b ∈ D.selmerSecondCocycles := sub_mem p.2 (coboundary_mem_cocycles_local D hb)
  have h0 : g.c2 (p.1 - b) = 0 := by rw [map_sub, hbq, sub_self]
  obtain ⟨p', hp', hfp⟩ := cocycle_descends_short_exact f g h hm h0
  rw [LinearMap.mem_range]
  refine ⟨Submodule.Quotient.mk ⟨p', hp'⟩, ?_⟩
  rw [Dat.Hom.h2, Submodule.mapQ_apply, Submodule.Quotient.eq]
  show f.c2 p' - p.1 ∈ D.selmerSecondCoboundaries
  rw [hfp, sub_sub_cancel_left]
  exact neg_mem hb
