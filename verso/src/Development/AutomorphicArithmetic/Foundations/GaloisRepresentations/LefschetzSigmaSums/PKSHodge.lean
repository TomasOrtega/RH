import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
open UpperTheory.Gal.LocalSmoothExtension

open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen UpperTheory.Gal.Int.Geo in
/- English proof (translation)
Introduce `hE hB hS hM hF hO p _ D G L sc lam anti`. Take `⟨k, hk⟩` from `hE p D G L sc lam anti`. Use `⟨k, ?_⟩` and prove the remaining obligations. Introduce `R _ _ gb T N J g θ f hf hs τ hρ ht σ i₀ h hh i`. Set `gb' : GBase D.toG ℂ` to `{ ρ := D.ρc ρ_root := D.toG.ρc_root t := fun i => (D.toG.tau i).comp (algebraMap _ _) t_ω := fun i => D.toG.tau_ω i comax := fun i j hij => by`.

Establish `ha : D.toG.a = 1` using `sc.a1`. Conclude with `absurd (Fin.ext (by have := i.2; have := j.2; omega)) hij }`. Establish `hstd : StdC D gb'` using `⟨rfl, fun _ _ => rfl⟩`. Take `⟨⟨X', lev', c1, c2, c3, c4, c5, c6⟩, hX, hl⟩` from `hB p D G L R gb k T τ gb' hρ.symm (fun i c => (ht i c).symm)`. Simplify using `only at hX`.

Substitute `hX` using the available equality. Consider the cases of `hl`. Establish `e : (fun (j : J) (y : G.GAf) => σ ((g j).fn y)) = fun j => (g j).fn`. Use function extensionality and compare the values at `j y`. Conclude with `map_natCast σ _`.

Establish `h1` using `hS σ p D G L lam (L.KN N.1) J (fun j => (g j).fn) θ f hs`. Rewrite `h1` using `[e]`. Establish `hfn : T.X.IsFn (T.lev N) f`. Use `(hF _ _ T.X (T.lev N) f).2 ?_ ?_` and prove the remaining obligations. Rewrite using `[T.K_eq]`.

Conclude with `hf.1`. Introduce `y hy`. Conclude with `(T.Δ_eq _).2 (hf.2 y hy)`. Establish `hfn' : T.X.IsFn (T.lev N) fun y => σ (f y)`. Take `⟨a1, a2, a3⟩` from `hfn`.

Use `⟨fun k hk y => ⟨?_, ?_⟩, fun y hy => a2 y ?_, a3.subset fun y hy => ?_⟩` and prove the remaining obligations. Use `show σ _ = σ _`. Rewrite using `[(a1 k hk y).1]`. Use `show σ _ = σ _`. Rewrite using `[(a1 k hk y).2]`.

Conclude with `fun h0 => hy (by show σ (f y) = 0; rw [h0, map_zero])`. Conclude with `fun h0 => hy (by show σ (f y.out) = 0; rw [h0, map_zero])`. Take `⟨b, x, hx, hx'⟩` from `hk gb' hstd ⟨_, T.lev, c1, c2, c3, c4, c5, c6⟩ N σ i₀ h hh J (fun j => (g j).fn) (fun j => σ (θ j)) (fun y => σ (f y)) (fun j => (hM p D G L R gb k T N J g j).1) hfn' h1 i`. Conclude with `hO p D G L R gb k T N J g τ _ (h i) b x hx hx'`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.kSHodge_of :
    HodgeEig → KSBc → SpecConj → MemOp → FnDecomp → OccOf → UpperTheory.Gal.Int.Geo.KSHodge := by
  intro hE hB hS hM hF hO p _ D G L sc lam anti
  obtain ⟨k, hk⟩ := hE p D G L sc lam anti
  refine ⟨k, ?_⟩
  intro R _ _ gb T N J g θ f hf hs τ hρ ht σ i₀ h hh i
  let gb' : GBase D.toG ℂ :=
    { ρ := D.ρc
      ρ_root := D.toG.ρc_root
      t := fun i => (D.toG.tau i).comp (algebraMap _ _)
      t_ω := fun i => D.toG.tau_ω i
      comax := fun i j hij => by
        have ha : D.toG.a = 1 := sc.a1
        exact absurd (Fin.ext (by have := i.2; have := j.2; omega)) hij }
  have hstd : StdC D gb' := ⟨rfl, fun _ _ => rfl⟩
  obtain ⟨⟨X', lev', c1, c2, c3, c4, c5, c6⟩, hX, hl⟩ :=
    hB p D G L R gb k T τ gb' hρ.symm (fun i c => (ht i c).symm)
  dsimp only at hX
  subst hX
  cases hl
  have e : (fun (j : J) (y : G.GAf) => σ ((g j).fn y)) = fun j => (g j).fn := by
    funext j y
    exact map_natCast σ _
  have h1 := hS σ p D G L lam (L.KN N.1) J (fun j => (g j).fn) θ f hs
  rw [e] at h1
  have hfn : T.X.IsFn (T.lev N) f := by
    refine (hF _ _ T.X (T.lev N) f).2 ?_ ?_
    · rw [T.K_eq]; exact hf.1
    · intro y hy
      exact (T.Δ_eq _).2 (hf.2 y hy)
  have hfn' : T.X.IsFn (T.lev N) fun y => σ (f y) := by
    obtain ⟨a1, a2, a3⟩ := hfn
    refine ⟨fun k hk y => ⟨?_, ?_⟩, fun y hy => a2 y ?_, a3.subset fun y hy => ?_⟩
    · show σ _ = σ _
      rw [(a1 k hk y).1]
    · show σ _ = σ _
      rw [(a1 k hk y).2]
    · exact fun h0 => hy (by show σ (f y) = 0; rw [h0, map_zero])
    · exact fun h0 => hy (by show σ (f y.out) = 0; rw [h0, map_zero])
  obtain ⟨b, x, hx, hx'⟩ := hk gb' hstd ⟨_, T.lev, c1, c2, c3, c4, c5, c6⟩ N σ i₀ h hh J (fun j => (g j).fn)
    (fun j => σ (θ j)) (fun y => σ (f y)) (fun j => (hM p D G L R gb k T N J g j).1) hfn' h1 i
  exact hO p D G L R gb k T N J g τ _ (h i) b x hx hx'
