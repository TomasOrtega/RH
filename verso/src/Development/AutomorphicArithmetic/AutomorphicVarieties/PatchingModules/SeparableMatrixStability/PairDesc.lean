import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlChBar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.GdetDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem md_single {B G G' : Type} [CommRing B] [Group G] [Group G'] (f : G →* G') (a : G) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.single a 1) = MonoidAlgebra.single (f a) 1 := by
  simp

/- English proof (translation)
Introduce `l _ L G G' g n O _ _ _ _ _ r r' B _ _ _ u H _ hHo hHη hHχ hker hc`. Take `⟨hc1, hc2, hc3⟩` from `hc`. Establish `hkill : ∀ k : G.G₀, g.p₀ k = 1 → u.D.Kills (MonoidAlgebra.single k 1 - 1)`. Introduce `k hk`. Establish `hk' : (k : G.Γ) ∈ PL l H`.

Rewrite using `[← hker, MonoidHom.mem_ker, ← g.coe_p₀, hk]`. Both sides reduce to the same expression. Establish `h1` using `pl_chBar l L G n O r B u H hHo hHη hHχ ∅ k hk'`. Use `UpperTheory.V.CA.d_closed u.D (maximalIdeal B) u.cont (u.D.CH ∪ ∅) ?_ _ h1` and prove the remaining obligations. Introduce and unpack `z (hz | hz)`.

Use `(UpperTheory.V.CA.d_toDet u.D z).2.2.2.1 ((UpperTheory.V.CA.d_ker _ z).1.1 (UpperTheory.V.CA.d_ch_ker _ ?_))` and prove the remaining obligations. Rewrite using `[UpperTheory.V.CA.d_toDet_CH]`. Conclude with `TwoSidedIdeal.subset_span hz`. Conclude with `hz.elim`. Take `⟨D', hD'⟩` from `gdet_desc n B G.G₀ G'.G₀ g.p₀ u.D g.p₀_surj hkill`.

Take `⟨-, hlam, htr, hmap, -, -⟩` from `comap_lam n B G.G₀ G'.G₀ g.p₀ D'`. Rewrite `hlam`, `htr`, `hmap` using `[hD']`. Take `⟨hstar, hoEl, -, -⟩` from `map_star l L G G' g n O B`. Use `⟨{ D := D', ψ := u.ψ, cont := ?_, red := ?_, psi := ?_, P := ?_, Ord := ?_, I := ?_ }, hD', rfl⟩` and prove the remaining obligations. Introduce `i`.

Use `(g.adicCont_iff _ fun a => D'.lam i (MonoidAlgebra.single a 1)).1 ?_` and prove the remaining obligations. Establish `: (fun a => D'.lam i (MonoidAlgebra.single (g.p₀ a) 1)) = fun a : G.G₀ => u.D.lam i (MonoidAlgebra.single a 1)` using `funext fun a => by`. Rewrite using `[hlam, md_single]`. Rewrite using `[this]`. Conclude with `u.cont i`.

Take `⟨-, -, -, -, hrep, hinj⟩` from `comap_lam n (ResidueField O) G.G₀ G'.G₀ g.p₀ r'.Dbar`. Use `(hinj g.p₀_surj).1 _ ?_` and prove the remaining obligations. Rewrite using `[← hmap]`. Use `u.red.trans ?_` and prove the remaining obligations. Unfold `Resid.Dbar`.

Rewrite using `[hrep]`. Use `congr 1`. Use extensionality with `a i j`. Simplify using `only [diagRep, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply, hc1]`. Introduce `v i`.

Use `⟨(u.psi v i).cont, fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← hc2]`. Conclude with `(u.psi v i).red a`. Rewrite using `[← hc3]`. Conclude with `(u.psi v i).mu a`.

Introduce `i a`. Take `⟨a, rfl⟩` from `g.p₀_surj a`. Rewrite using `[← md_single, ← hstar, ← hlam, ← hlam]`. Conclude with `u.P i a`. Introduce `v a h`.

Take `⟨h, rfl⟩` from `g.p₀_surj h`. Rewrite using `[← md_single, ← hoEl, ← map_mul, ← htr]`. Conclude with `u.Ord v a h`. Introduce and unpack `w _ ⟨⟨a, ha, rfl⟩, ha'⟩ h`. Take `⟨h, rfl⟩` from `g.p₀_surj h`.

Establish `hmem : G.φu w a ∈ r.Ip w`. Use `⟨⟨a, ha, rfl⟩, Subgroup.mem_iInf.2 fun i => ?_⟩` and prove the remaining obligations. Use `Subgroup.mem_iInf.1 ha' i` as an intermediate fact. Rewrite `this`, the goal using `[MonoidHom.mem_ker]`. Rewrite using `[hc1, MonoidHom.comp_apply, g.p₀_φu]`.

Conclude with `this`. Use `u.I w _ hmem h` as an intermediate fact. Rewrite `this` using `[htr, map_mul, map_sub, map_one, md_single, md_single, g.p₀_φu]`. Conclude with `this`.
-/
theorem UpperTheory.V.Pa.pair_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G.frame O n) (r' : Resid G'.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (∀ a : G.G₀, (a : G.Γ) ∈ H → ∀ i, r.chib i a = 1) → g.p.ker = PL l H → Glob.Compat g r r' → ∃ u' : Pair r' B, u'.D.comap g.p₀ = u.D ∧ u'.ψ = u.ψ := by
  intro l _ L G G' g n O _ _ _ _ _ r r' B _ _ _ u H _ hHo hHη hHχ hker hc
  obtain ⟨hc1, hc2, hc3⟩ := hc
  have hkill : ∀ k : G.G₀, g.p₀ k = 1 → u.D.Kills (MonoidAlgebra.single k 1 - 1) := by
    intro k hk
    have hk' : (k : G.Γ) ∈ PL l H := by
      rw [← hker, MonoidHom.mem_ker, ← g.coe_p₀, hk]; rfl
    have h1 := pl_chBar l L G n O r B u H hHo hHη hHχ ∅ k hk'
    refine UpperTheory.V.CA.d_closed u.D (maximalIdeal B) u.cont (u.D.CH ∪ ∅) ?_ _ h1
    rintro z (hz | hz)
    · refine (UpperTheory.V.CA.d_toDet u.D z).2.2.2.1 ((UpperTheory.V.CA.d_ker _ z).1.1 (UpperTheory.V.CA.d_ch_ker _ ?_))
      rw [UpperTheory.V.CA.d_toDet_CH]
      exact TwoSidedIdeal.subset_span hz
    · exact hz.elim
  obtain ⟨D', hD'⟩ := gdet_desc n B G.G₀ G'.G₀ g.p₀ u.D g.p₀_surj hkill
  obtain ⟨-, hlam, htr, hmap, -, -⟩ := comap_lam n B G.G₀ G'.G₀ g.p₀ D'
  rw [hD'] at hlam htr hmap
  obtain ⟨hstar, hoEl, -, -⟩ := map_star l L G G' g n O B
  refine ⟨{ D := D', ψ := u.ψ, cont := ?_, red := ?_, psi := ?_, P := ?_, Ord := ?_, I := ?_ }, hD', rfl⟩
  · intro i
    refine (g.adicCont_iff _ fun a => D'.lam i (MonoidAlgebra.single a 1)).1 ?_
    have : (fun a => D'.lam i (MonoidAlgebra.single (g.p₀ a) 1)) =
        fun a : G.G₀ => u.D.lam i (MonoidAlgebra.single a 1) := funext fun a => by
      rw [hlam, md_single]
    rw [this]
    exact u.cont i
  · obtain ⟨-, -, -, -, hrep, hinj⟩ := comap_lam n (ResidueField O) G.G₀ G'.G₀ g.p₀ r'.Dbar
    refine (hinj g.p₀_surj).1 _ ?_
    rw [← hmap]
    refine u.red.trans ?_
    unfold Resid.Dbar
    rw [hrep]
    congr 1
    ext a i j
    simp only [diagRep, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply, hc1]
  · intro v i
    refine ⟨(u.psi v i).cont, fun a => ?_, fun a => ?_⟩
    · rw [← hc2]; exact (u.psi v i).red a
    · rw [← hc3]; exact (u.psi v i).mu a
  · intro i a
    obtain ⟨a, rfl⟩ := g.p₀_surj a
    rw [← md_single, ← hstar, ← hlam, ← hlam]
    exact u.P i a
  · intro v a h
    obtain ⟨h, rfl⟩ := g.p₀_surj h
    rw [← md_single, ← hoEl, ← map_mul, ← htr]
    exact u.Ord v a h
  · rintro w _ ⟨⟨a, ha, rfl⟩, ha'⟩ h
    obtain ⟨h, rfl⟩ := g.p₀_surj h
    have hmem : G.φu w a ∈ r.Ip w := by
      refine ⟨⟨a, ha, rfl⟩, Subgroup.mem_iInf.2 fun i => ?_⟩
      have := Subgroup.mem_iInf.1 ha' i
      rw [MonoidHom.mem_ker] at this ⊢
      rw [hc1, MonoidHom.comp_apply, g.p₀_φu]
      exact this
    have := u.I w _ hmem h
    rw [htr, map_mul, map_sub, map_one, md_single, md_single, g.p₀_φu] at this
    exact this
