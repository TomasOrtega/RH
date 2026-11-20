import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.ExtRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `O Γ k _ _ _ _ _ _ Φ a l _ _ hfin hok 𝒩 hG w w' J _ y hy`. Take `⟨M, i1, i2, i3, i4, i5, ρ, p, q, m0, hc, hN, hp, hq, hm0, hpm⟩` from `Gys.extRep Φ a l hfin hok.lc w w' J y hy`. Take `⟨N', hN', c, hcZ, hc0, hloc, g, hg1, hcg, hspan⟩` from `hG M ρ hc (fun g hg => hN g (hok.kill g hg) (fun j => (hy j).kill g hg)) m0 hm0`. Take `⟨hcont, hcoc⟩` from `(mem_Z1_iff_cocycle ρ c).1 hcZ`. Establish `hlc : IsLocallyConstant c` using `(IsLocallyConstant.iff_continuous c).2 hcont`.

Establish `hrt : ∀ u, (Φ.wN N').rt u = Φ.rt u` using `fun u => rfl`. Use `choose mm hmm using hloc`. Establish `hpg : p (c g) ≠ 0` using `hpm _ hspan hcg`. Use `⟨N', hN', fun s => p (c s), fun v => -p (mm v), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `⟨hlc.comp p, ?_, ?_⟩` and prove the remaining obligations.

Introduce `s t`. Rewrite using `[hrt, hcoc, map_add, hp]`. Introduce `s hs`. Simplify using `[hc0 s hs]`. Introduce `v s hs show p (c s) = -p (mm v) - a ↑((Φ.rt w) s) * -p (mm v)`.

Rewrite using `[hmm v s hs, map_sub, hp]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨g, ?_, hpg⟩` and prove the remaining obligations. Establish `h` using `hp g (c g)`. Rewrite `h` using `[hg1]`.

Express the relevant statement in the definitionally equal form `p (c g) = _ at h`. Establish `h2 : (a ↑((Φ.rt w) g) - 1) * p (c g) = 0` using `by linear_combination -h`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `sub_eq_zero.1 h3`. Conclude with `absurd h3 hpg`.

Introduce `j`. Use `⟨fun s => q j (c s), hlc.comp (q j), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s t`. Simplify using `only [hrt]`. Rewrite using `[hcoc, map_add, hq]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `s hs`. Simplify using `[hc0 s hs]`. Introduce `v`. Use `⟨-q j (mm v), fun s hs => ?_⟩` and prove the remaining obligations.

Simplify using `only [hrt]`. Rewrite using `[hmm v s hs, map_sub, hq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Ws.Gys.cupRaw :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (l : ℕ) [Fact l.Prime] [CharP k l], (Set.range a).Finite → Φ.Ok a → ∀ 𝒩 : Set Γ → Prop, Φ.Gys l 𝒩 → ∀ (w w' : ℤ × ℤ) (J : Type) [Finite J] (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j)) →
      ∃ N', 𝒩 N' ∧ ∃ (x : Γ → k) (m : Φ.ι → k), (Φ.wN N').Coc a w x ∧ Φ.LocTriv a w x m ∧ (∃ g, a (Φ.rt w g) = 1 ∧ x g ≠ 0) ∧
        ∀ j, ∃ z, (Φ.wN N').Cup a w w' x (y j) z m := by
  intro O Γ k _ _ _ _ _ _ Φ a l _ _ hfin hok 𝒩 hG w w' J _ y hy
  obtain ⟨M, i1, i2, i3, i4, i5, ρ, p, q, m0, hc, hN, hp, hq, hm0, hpm⟩ :=
    Gys.extRep Φ a l hfin hok.lc w w' J y hy
  obtain ⟨N', hN', c, hcZ, hc0, hloc, g, hg1, hcg, hspan⟩ :=
    hG M ρ hc (fun g hg => hN g (hok.kill g hg) (fun j => (hy j).kill g hg)) m0 hm0
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle ρ c).1 hcZ
  have hlc : IsLocallyConstant c := (IsLocallyConstant.iff_continuous c).2 hcont
  have hrt : ∀ u, (Φ.wN N').rt u = Φ.rt u := fun u => rfl
  choose mm hmm using hloc
  have hpg : p (c g) ≠ 0 := hpm _ hspan hcg
  refine ⟨N', hN', fun s => p (c s), fun v => -p (mm v), ?_, ?_, ?_, ?_⟩
  · refine ⟨hlc.comp p, ?_, ?_⟩
    · intro s t
      rw [hrt, hcoc, map_add, hp]
    · intro s hs
      simp [hc0 s hs]
  · intro v s hs
    show p (c s) = -p (mm v) - a ↑((Φ.rt w) s) * -p (mm v)
    rw [hmm v s hs, map_sub, hp]
    ring
  · refine ⟨g, ?_, hpg⟩
    have h := hp g (c g)
    rw [hg1] at h
    change p (c g) = _ at h
    have h2 : (a ↑((Φ.rt w) g) - 1) * p (c g) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hpg
  · intro j
    refine ⟨fun s => q j (c s), hlc.comp (q j), ?_, ?_, ?_⟩
    · intro s t
      simp only [hrt]
      rw [hcoc, map_add, hq]
      ring
    · intro s hs
      simp [hc0 s hs]
    · intro v
      refine ⟨-q j (mm v), fun s hs => ?_⟩
      simp only [hrt]
      rw [hmm v s hs, map_sub, hq]
      ring
