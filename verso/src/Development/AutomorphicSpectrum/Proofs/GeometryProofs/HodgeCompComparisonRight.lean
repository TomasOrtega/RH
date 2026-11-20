import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegularStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VbGen

/- English proof (translation)
Establish `key : ∀ c c' : Fin r → V, flagStep Ω c k ≤ flagStep Ω c' k → flagStep Ω' (fun a => j (c a)) k ≤ flagStep Ω' (fun a => j (c' a)) k`. Introduce `c c' hle`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Establish `hmem : c a ∈ flagStep Ω c' k` using `hle (Submodule.subset_span ⟨a, ha, rfl⟩)`.

Use `show j (c a) ∈ _`. Use `Submodule.span_induction (p := fun v _ => j v ∈ flagStep Ω' (fun a => j (c' a)) k) ?_ ?_ ?_ ?_ hmem` and prove the remaining obligations. Introduce and unpack `_ ⟨d, hd, rfl⟩`. Conclude with `Submodule.subset_span ⟨d, hd, rfl⟩`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `add_mem hx hy`. Introduce `t x _ hx`. Rewrite using `[hj]`.

Conclude with `Submodule.smul_mem _ _ hx`. Conclude with `le_antisymm (key _ _ h.le) (key _ _ h.ge)`.
-/
theorem flagStep_comp {Ω Ω' V V' : Type} [Field Ω] [Field Ω'] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω' V'] (i : Ω →+* Ω') (j : V →+ V') (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e) {r : ℕ}
    (b b' : Fin r → V) (k : ℕ) (h : flagStep Ω b k = flagStep Ω b' k) :
    flagStep Ω' (fun a => j (b a)) k = flagStep Ω' (fun a => j (b' a)) k := by
  have key : ∀ c c' : Fin r → V, flagStep Ω c k ≤ flagStep Ω c' k →
      flagStep Ω' (fun a => j (c a)) k ≤ flagStep Ω' (fun a => j (c' a)) k := by
    intro c c' hle
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have hmem : c a ∈ flagStep Ω c' k := hle (Submodule.subset_span ⟨a, ha, rfl⟩)
    show j (c a) ∈ _
    refine Submodule.span_induction (p := fun v _ => j v ∈ flagStep Ω' (fun a => j (c' a)) k) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨d, hd, rfl⟩
      exact Submodule.subset_span ⟨d, hd, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro t x _ hx
      rw [hj]
      exact Submodule.smul_mem _ _ hx
  exact le_antisymm (key _ _ h.le) (key _ _ h.ge)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `Submodule.span_induction (p := fun v _ => j v ∈ Submodule.span R' (Set.range fun a => j (b a))) ?_ ?_ ?_ ?_ hv` and prove the remaining obligations. Introduce and unpack `_ ⟨d, rfl⟩`.

Conclude with `Submodule.subset_span ⟨d, rfl⟩`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `add_mem hx hy`.

Introduce `t x _ hx`. Establish `h1 : j (t • x) = (⟨i t, hR t t.2⟩ : R') • j x` using `hj (t : Ω) x`. Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ _ hx`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Submodule.subset_span ⟨b a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩`.
-/
theorem span_image_span {Ω Ω' V V' : Type} [Field Ω] [Field Ω'] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω' V'] (i : Ω →+* Ω') (j : V →+ V') (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e)
    (R : Subring Ω) (R' : Subring Ω') (hR : ∀ a ∈ R, i a ∈ R') {r : ℕ} (b : Fin r → V) :
    Submodule.span R' (j '' (Submodule.span R (Set.range b) : Set V)) =
      Submodule.span R' (Set.range fun a => j (b a)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    refine Submodule.span_induction
      (p := fun v _ => j v ∈ Submodule.span R' (Set.range fun a => j (b a))) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨d, rfl⟩
      exact Submodule.subset_span ⟨d, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro t x _ hx
      have h1 : j (t • x) = (⟨i t, hR t t.2⟩ : R') • j x := hj (t : Ω) x
      rw [h1]
      exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨b a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩

/- English proof (translation)
Establish `hn0 : 0 < (NumberField.discr F).natAbs` using `Int.natAbs_pos.2 (NumberField.discr_ne_zero F)`. Take `⟨-, -, hu⟩` from `h _ hn0`. Break down `Int.natAbs_eq (NumberField.discr F) with e | e` into its components or cases. Rewrite using `[e]`. Simplify using `using hu`.

Rewrite using `[e]`. Simplify using `using (regAt ξ p).neg_mem hu`.
-/
theorem discr_inv_mem {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ)
    (F : Type) [Field F] [NumberField F] (h : ∀ n : ℕ, 0 < n → unitAt ξ p (n : Ω)) :
    (((NumberField.discr F : ℤ) : Ω))⁻¹ ∈ regAt ξ p := by
  have hn0 : 0 < (NumberField.discr F).natAbs := Int.natAbs_pos.2 (NumberField.discr_ne_zero F)
  obtain ⟨-, -, hu⟩ := h _ hn0
  rcases Int.natAbs_eq (NumberField.discr F) with e | e
  · rw [e]; simpa using hu
  · rw [e]
    simpa using (regAt ξ p).neg_mem hu

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A Fl B i h jA hdom hf hcst hext hpt hρ hlat q hq s`. Introduce `q' hq'`. Take `rfl : q' = q` from `hq'`. Use `haveI : CharZero Ω₁ := charZero_of_injective_ringHom A.cst.injective`. Establish `hgenA` using `A.tie.gen`.

Establish `hgenB` using `B.tie.gen`. Take `⟨hsp, hreg, hun⟩` from `RegAtDom.regAt_dominates A.X Ω₁ A.ξ B.X Ω B.ξ h i hdom q'`. Establish `hunit : ∀ n : ℕ, 0 < n → unitAt A.ξ ⟨h q'.1, hsp⟩ (n : Ω₁)` using `fun n hn => hun hgenB _ (natCast_mem _ n) (by simpa using hq n hn)`. Establish `hVA : A.V s ⟨h q'.1, hsp⟩ = A.dR s ⟨h q'.1, hsp⟩` using `Lat.patch_of_not S₀ _ _ fun r hr hfib => hfib (hunit r (A.S_prime r hr).pos)`. Establish `hVB : B.V s q' = B.dR s q'` using `Lat.patch_of_not S _ _ fun r hr hfib => hfib (hq r (B.S_prime r hr).pos)`.

Establish `hdisc` using `discr_inv_mem ⟨h q'.1, hsp⟩ E hunit`. Establish `hint : ∀ a, A.emb s a ∈ regAt A.ξ ⟨h q'.1, hsp⟩` using `fun a => GlobalTheory.T.integral_element_regular A.X Ω₁ A.ξ ⟨h q'.1, hsp⟩ hgenA (A.normal (h q'.1)).2 _ ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)`. Take `⟨U, hU, b, hb, hfr⟩` from `Fl.sub s ⟨h q'.1, hsp⟩ trivial`. Take `⟨hli, hbs⟩` from `hfr ⟨h q'.1, hsp⟩ trivial hU`. Use `⟨⊤, trivial, fun a => jA (b a), fun k => flagStep_comp i jA hext.1 _ _ k (hb k), ?_⟩` and prove the remaining obligations.

Introduce `q'' hq'' _`. Rewrite using `[show q'' = q' from hq'']`. Use `⟨hext.2 _ b hli, ?_⟩` and prove the remaining obligations. Establish `key` using `GlobalTheory.T.lattice_eigen_field_extension E Ω₁ Ω i A.Li B.Li jA A.ρ B.ρ (A.emb s) _ _ (A.M.lat ⟨h q'.1, hsp⟩) hext (fun a e => (hρ a e).symm) hreg (fun a e he => GlobalTheory.T.lie_lattice_stable_under_action A.X Ω₁ A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act _ a e he) hint hdi …`. Establish `hem : B.emb s = i.comp (A.emb s)` using `by show B.cst.comp _ = i.comp (A.cst.comp _)`.

Rewrite using `[hcst]`. Both sides reduce to the same expression. Establish `hL : B.M.lat q' = Submodule.span (regAt B.ξ q') (jA '' (A.M.lat ⟨h q'.1, hsp⟩ : Set A.Li))`. Rewrite using `[hlat]`. Use `show Lat.pull _ _ _ _ _ = _`.

Unfold `Lat.pull`. Use `congr 1`. Use extensionality with `e'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, e, he, rfl⟩`.

Conclude with `⟨e, he, rfl⟩`. Introduce and unpack `⟨e, he, rfl⟩`. Conclude with `⟨hsp, e, he, rfl⟩`. Establish `hA : A.M.lat ⟨h q'.1, hsp⟩ ⊓ (eigSp A.ρ (A.emb s)).restrictScalars (regAt A.ξ ⟨h q'.1, hsp⟩) = Submodule.span (regAt A.ξ ⟨h q'.1, hsp⟩) (Set.range b)` using `hVA.symm.trans hbs`. Rewrite using `[hVB]`.

Use `show B.M.lat q' ⊓ (eigSp B.ρ (B.emb s)).restrictScalars (regAt B.ξ q') = _`. Rewrite using `[hL, hem, key, hA]`. Conclude with `span_image_span i jA hext.1 _ _ hreg b`.
-/
theorem isFlagVBOn_genFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → B.M.lat = A.M.lat.pull B.ξ h jA → ∀ q ∈ genFib B.ξ, ∀ s, (B.V s).IsFlagVBOn {q} (fun a => jA (Fl.b s a)) := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A Fl B i h jA hdom hf hcst hext hpt hρ hlat q hq s
  intro q' hq'
  obtain rfl : q' = q := hq'
  haveI : CharZero Ω₁ := charZero_of_injective_ringHom A.cst.injective
  have hgenA := A.tie.gen
  have hgenB := B.tie.gen
  obtain ⟨hsp, hreg, hun⟩ := RegAtDom.regAt_dominates A.X Ω₁ A.ξ B.X Ω B.ξ h i hdom q'
  have hunit : ∀ n : ℕ, 0 < n → unitAt A.ξ ⟨h q'.1, hsp⟩ (n : Ω₁) := fun n hn =>
    hun hgenB _ (natCast_mem _ n) (by simpa using hq n hn)
  have hVA : A.V s ⟨h q'.1, hsp⟩ = A.dR s ⟨h q'.1, hsp⟩ :=
    Lat.patch_of_not S₀ _ _ fun r hr hfib => hfib (hunit r (A.S_prime r hr).pos)
  have hVB : B.V s q' = B.dR s q' :=
    Lat.patch_of_not S _ _ fun r hr hfib => hfib (hq r (B.S_prime r hr).pos)
  have hdisc := discr_inv_mem ⟨h q'.1, hsp⟩ E hunit
  have hint : ∀ a, A.emb s a ∈ regAt A.ξ ⟨h q'.1, hsp⟩ := fun a =>
    GlobalTheory.T.integral_element_regular A.X Ω₁ A.ξ ⟨h q'.1, hsp⟩ hgenA (A.normal (h q'.1)).2 _
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)
  obtain ⟨U, hU, b, hb, hfr⟩ := Fl.sub s ⟨h q'.1, hsp⟩ trivial
  obtain ⟨hli, hbs⟩ := hfr ⟨h q'.1, hsp⟩ trivial hU
  refine ⟨⊤, trivial, fun a => jA (b a), fun k => flagStep_comp i jA hext.1 _ _ k (hb k), ?_⟩
  intro q'' hq'' _
  rw [show q'' = q' from hq'']
  refine ⟨hext.2 _ b hli, ?_⟩
  have key := GlobalTheory.T.lattice_eigen_field_extension E Ω₁ Ω i A.Li B.Li jA A.ρ B.ρ (A.emb s) _ _ (A.M.lat ⟨h q'.1, hsp⟩) hext
    (fun a e => (hρ a e).symm) hreg
    (fun a e he => GlobalTheory.T.lie_lattice_stable_under_action A.X Ω₁ A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act _ a e he) hint hdisc
  have hem : B.emb s = i.comp (A.emb s) := by
    show B.cst.comp _ = i.comp (A.cst.comp _)
    rw [hcst]; rfl
  have hL : B.M.lat q' = Submodule.span (regAt B.ξ q') (jA '' (A.M.lat ⟨h q'.1, hsp⟩ : Set A.Li)) := by
    rw [hlat]
    show Lat.pull _ _ _ _ _ = _
    unfold Lat.pull
    congr 1
    ext e'
    constructor
    · rintro ⟨_, e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨hsp, e, he, rfl⟩
  have hA : A.M.lat ⟨h q'.1, hsp⟩ ⊓ (eigSp A.ρ (A.emb s)).restrictScalars (regAt A.ξ ⟨h q'.1, hsp⟩) =
      Submodule.span (regAt A.ξ ⟨h q'.1, hsp⟩) (Set.range b) := hVA.symm.trans hbs
  rw [hVB]
  show B.M.lat q' ⊓ (eigSp B.ρ (B.emb s)).restrictScalars (regAt B.ξ q') = _
  rw [hL, hem, key, hA]
  exact span_image_span i jA hext.1 _ _ hreg b

end GlobalTheory.CompanionTheory.Ar.VbGen
