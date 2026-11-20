import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdKill
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

/- English proof (translation)
Introduce `l _ L G G0 h n x X _ _ X'' _ _ D D'' o o'' g hg hur w y'' hy`. Establish `hs : ∀ w, Function.Surjective (g.fq w)`. Introduce `w q`. Take `⟨m, rfl⟩` from `D''.surj w q`. Take `⟨m, rfl⟩` from `hg m`.

Conclude with `⟨D.π w m, g.comm w m⟩`. Establish `top : ∀ w, (∀ s, s ∈ (plOf G).J w) → ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s`. Introduce and unpack `w hw y'' ⟨-, Y, hY⟩`. Take `⟨Y, rfl⟩` from `hs _ Y`. Use `⟨d0 (D.Q w).ρ Y, ⟨coboundaries_le_cocycles _ (D.Q w).cont ⟨Y, rfl⟩, Y, fun s _ => amitsur_d0_apply _ _ _⟩, fun s => ?_⟩` and prove the remaining obligations.

Rewrite using `[hY s (hw s), amitsur_d0_apply, map_sub, g.equivq]`. Break down `w with v | u` into its components or cases. Conclude with `top (inV G v) (fun s => Subgroup.mem_top (G := L.Gv v) s) y'' hy`. Take `⟨hz, Y, hY⟩` from `hy`. Take `⟨-, k1, k2⟩` from `odKill l L G G0 h n x X D o`.

Take `⟨-, -, k3⟩` from `odKill l L G G0 h n x X'' D'' o''`. Take `⟨y, a1, a2, a3⟩` from `(hur u x.A (D.Q (inU G u)) (k1 _) (k2 u)).2 (D''.Q (inU G u)) (g.fq (inU G u)) (g.equivq (inU G u)) (hs _) y'' hz (fun s hs => (hY s hs).trans (sub_eq_zero.2 (k3 u s hs Y)))`. Conclude with `⟨y, ⟨a1, 0, fun s hs => (a2 s hs).trans (sub_eq_zero.2 (k2 u s hs 0)).symm⟩, a3⟩`.
-/
theorem UpperTheory.V.Pa.B2.odLam :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (X'' : Type) [CommRing X''] [Algebra x.A X''] (D D'' : Dat x.A (plOf G)) (_ : IsOd h x X D) (_ : IsOd h x X'' D'') (g : D.Hom D''), Function.Surjective g.f → (∀ u, UrAx l (L.Ju u)) → ∀ w, ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s := by
  intro l _ L G G0 h n x X _ _ X'' _ _ D D'' o o'' g hg hur w y'' hy
  have hs : ∀ w, Function.Surjective (g.fq w) := by
    intro w q
    obtain ⟨m, rfl⟩ := D''.surj w q
    obtain ⟨m, rfl⟩ := hg m
    exact ⟨D.π w m, g.comm w m⟩
  have top : ∀ w, (∀ s, s ∈ (plOf G).J w) → ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s := by
    rintro w hw y'' ⟨-, Y, hY⟩
    obtain ⟨Y, rfl⟩ := hs _ Y
    refine ⟨d0 (D.Q w).ρ Y, ⟨coboundaries_le_cocycles _ (D.Q w).cont ⟨Y, rfl⟩, Y, fun s _ => amitsur_d0_apply _ _ _⟩, fun s => ?_⟩
    rw [hY s (hw s), amitsur_d0_apply, map_sub, g.equivq]
  rcases w with v | u
  · exact top (inV G v) (fun s => Subgroup.mem_top (G := L.Gv v) s) y'' hy
  · obtain ⟨hz, Y, hY⟩ := hy
    obtain ⟨-, k1, k2⟩ := odKill l L G G0 h n x X D o
    obtain ⟨-, -, k3⟩ := odKill l L G G0 h n x X'' D'' o''
    obtain ⟨y, a1, a2, a3⟩ := (hur u x.A (D.Q (inU G u)) (k1 _) (k2 u)).2 (D''.Q (inU G u)) (g.fq (inU G u))
      (g.equivq (inU G u)) (hs _) y'' hz (fun s hs => (hY s hs).trans (sub_eq_zero.2 (k3 u s hs Y)))
    exact ⟨y, ⟨a1, 0, fun s hs => (a2 s hs).trans (sub_eq_zero.2 (k2 u s hs 0)).symm⟩, a3⟩
