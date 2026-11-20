import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmoothStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

/- English proof (translation)
Conclude with `congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hq q.2 t)`.
-/
theorem genMap_germ (W : X.Opens) (t : Γ(X, W)) (q : Cpt ξ) (hq : q.1 ∈ W) (hW : genPt ξ ∈ W) :
    genMap ξ q (X.presheaf.germ W q.1 hq t) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hW t) := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hq q.2 t)

/- English proof (translation)
Take `⟨s, rfl⟩` from `h`. Take `⟨W, hp, t, rfl⟩` from `TopCat.Presheaf.exists_germ_eq X.presheaf s`. Establish `hW : genPt ξ ∈ W` using `p.2.mem_open W.isOpen hp`. Use `⟨W, hp, fun q hq => ⟨X.presheaf.germ W q.1 hq t, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[genMap_germ W t q hq hW, genMap_germ W t p hp hW]`.
-/
theorem regAt_near {p : Cpt ξ} {a : Ω} (h : a ∈ regAt ξ p) :
    ∃ W : X.Opens, p.1 ∈ W ∧ ∀ q : Cpt ξ, q.1 ∈ W → a ∈ regAt ξ q := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨W, hp, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf s
  have hW : genPt ξ ∈ W := p.2.mem_open W.isOpen hp
  refine ⟨W, hp, fun q hq => ⟨X.presheaf.germ W q.1 hq t, ?_⟩⟩
  rw [genMap_germ W t q hq hW, genMap_germ W t p hp hW]

/- English proof (translation)
Proceed by induction on `A using Finset.induction_on with`. Consider the case `empty => exact ⟨⊤, trivial, fun _ _ _ ha => absurd ha (Finset.notMem_empty _)⟩`. Consider the case `insert a A _ ih`. Take `⟨W, hp, hW⟩` from `ih fun b hb => h b (Finset.mem_insert_of_mem hb)`. Take `⟨W', hp', hW'⟩` from `regAt_near (h a (Finset.mem_insert_self a A))`.

Use `⟨W ⊓ W', ⟨hp, hp'⟩, fun q hq b hb => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hb with rfl | hb` into its components or cases. Conclude with `hW' q hq.2`. Conclude with `hW q hq.1 b hb`.
-/
theorem regAt_near_finset {p : Cpt ξ} (A : Finset Ω) (h : ∀ a ∈ A, a ∈ regAt ξ p) :
    ∃ W : X.Opens, p.1 ∈ W ∧ ∀ q : Cpt ξ, q.1 ∈ W → ∀ a ∈ A, a ∈ regAt ξ q := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, fun _ _ _ ha => absurd ha (Finset.notMem_empty _)⟩
  | insert a A _ ih =>
    obtain ⟨W, hp, hW⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    obtain ⟨W', hp', hW'⟩ := regAt_near (h a (Finset.mem_insert_self a A))
    refine ⟨W ⊓ W', ⟨hp, hp'⟩, fun q hq b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hW' q hq.2
    · exact hW q hq.1 b hb

/- English proof (translation)
Take `⟨U, hpU, b, -, hb⟩` from `(GlobalTheory.T.lie_lattice_vector_bundle_of_smooth X G g Ω ξ Li M hξ hG).1 p (Set.mem_univ p)`. Establish `hbp` using `(hb p (Set.mem_univ p) hpU).2`. Establish `hc : ∀ j, ∃ c : Fin g → regAt ξ p, ∑ s, c s • b s = S j` using `fun j => by`. Use `hS j` as an intermediate fact. Rewrite `this` using `[hbp]`.

Conclude with `(Submodule.mem_span_range_iff_exists_fun _).1 this`. Use `choose c hc using hc`. Establish `hΦb : ∀ j s, Φ j (b s) ∈ regAt ξ p` using `fun j s => hΦ j _ (by rw [hbp]; exact Submodule.subset_span ⟨s, rfl⟩)`. Take `⟨W, hpW, hW⟩` from `regAt_near_finset (ξ := ξ) (p := p) (Finset.univ.image (fun js : Fin n × Fin g => (c js.1 js.2 : Ω)) ∪ Finset.univ.image (fun js : Fin n × Fin g => Φ js.1 (b js.2))) (by`. Introduce `a ha`.

Break down `Finset.mem_union.1 ha with ha | ha` into its components or cases. Take `⟨js, -, rfl⟩` from `Finset.mem_image.1 ha`. Conclude with `(c js.1 js.2).2`. Take `⟨js, -, rfl⟩` from `Finset.mem_image.1 ha`. Conclude with `hΦb js.1 js.2)`.

Use `⟨U ⊓ W, ⟨hpU, hpW⟩, fun q hq => ?_⟩` and prove the remaining obligations. Establish `hbq` using `(hb q (Set.mem_univ q) hq.1).2`. Establish `hcq : ∀ j s, (c j s : Ω) ∈ regAt ξ q` using `fun j s => hW q hq.2 _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(j, s), Finset.mem_univ _, rfl⟩))`. Establish `hΦq : ∀ j s, Φ j (b s) ∈ regAt ξ q` using `fun j s => hW q hq.2 _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(j, s), Finset.mem_univ _, rfl⟩))`. Use `⟨fun j => ?_, fun j e he => ?_⟩` and prove the remaining obligations.

Rewrite using `[hbq, ← hc j]`. Use `Submodule.sum_mem _ fun s _ => ?_` and prove the remaining obligations. Establish `: (c j s) • b s = (⟨c j s, hcq j s⟩ : regAt ξ q) • b s` using `rfl`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)`.

Rewrite `he` using `[hbq]`. Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨s, rfl⟩` from `hx`. Conclude with `hΦq j s`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simpa using add_mem hx hy`. Consider the case `smul r x _ hx`. Establish `: Φ j (r • x) = (r : Ω) * Φ j x` using `by show Φ j ((r : Ω) • x) = _`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `mul_mem r.2 hx`.
-/
theorem lie_near (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (g : ℕ) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    (hξ : IsCptGen ξ) (hG : SmoothOfRelativeDimension g G.hom)
    (p : Cpt ξ) (n : ℕ) (S : Fin n → Li) (Φ : Fin n → Module.Dual Ω Li)
    (hS : ∀ j, S j ∈ M.lat p) (hΦ : ∀ j, ∀ e ∈ M.lat p, Φ j e ∈ regAt ξ p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
      (∀ j, S j ∈ M.lat q) ∧ ∀ j, ∀ e ∈ M.lat q, Φ j e ∈ regAt ξ q := by
  classical
  obtain ⟨U, hpU, b, -, hb⟩ := (GlobalTheory.T.lie_lattice_vector_bundle_of_smooth X G g Ω ξ Li M hξ hG).1 p (Set.mem_univ p)
  have hbp := (hb p (Set.mem_univ p) hpU).2
  have hc : ∀ j, ∃ c : Fin g → regAt ξ p, ∑ s, c s • b s = S j := fun j => by
    have := hS j
    rw [hbp] at this
    exact (Submodule.mem_span_range_iff_exists_fun _).1 this
  choose c hc using hc
  have hΦb : ∀ j s, Φ j (b s) ∈ regAt ξ p := fun j s =>
    hΦ j _ (by rw [hbp]; exact Submodule.subset_span ⟨s, rfl⟩)
  obtain ⟨W, hpW, hW⟩ := regAt_near_finset (ξ := ξ) (p := p)
    (Finset.univ.image (fun js : Fin n × Fin g => (c js.1 js.2 : Ω)) ∪
      Finset.univ.image (fun js : Fin n × Fin g => Φ js.1 (b js.2))) (by
      intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · obtain ⟨js, -, rfl⟩ := Finset.mem_image.1 ha
        exact (c js.1 js.2).2
      · obtain ⟨js, -, rfl⟩ := Finset.mem_image.1 ha
        exact hΦb js.1 js.2)
  refine ⟨U ⊓ W, ⟨hpU, hpW⟩, fun q hq => ?_⟩
  have hbq := (hb q (Set.mem_univ q) hq.1).2
  have hcq : ∀ j s, (c j s : Ω) ∈ regAt ξ q := fun j s =>
    hW q hq.2 _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(j, s), Finset.mem_univ _, rfl⟩))
  have hΦq : ∀ j s, Φ j (b s) ∈ regAt ξ q := fun j s =>
    hW q hq.2 _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(j, s), Finset.mem_univ _, rfl⟩))
  refine ⟨fun j => ?_, fun j e he => ?_⟩
  · rw [hbq, ← hc j]
    refine Submodule.sum_mem _ fun s _ => ?_
    have : (c j s) • b s = (⟨c j s, hcq j s⟩ : regAt ξ q) • b s := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · rw [hbq] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact hΦq j s
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul r x _ hx =>
      have : Φ j (r • x) = (r : Ω) * Φ j x := by
        show Φ j ((r : Ω) • x) = _
        simp
      rw [this]
      exact mul_mem r.2 hx

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
