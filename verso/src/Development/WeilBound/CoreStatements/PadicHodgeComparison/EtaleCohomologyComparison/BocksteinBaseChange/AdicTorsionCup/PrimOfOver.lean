import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.AdicGeo

/- English proof (translation)
Substitute `hf` using the available equality. Establish `key : (pullback.lift (pullback.fst (u ≫ f) g ≫ u) (pullback.snd (u ≫ f) g) (by rw [Category.assoc, pullback.condition]) : pullback (u ≫ f) g ⟶ pullback f g) = pullback.map (u ≫ f) g f g u (𝟙 Z) (𝟙 S) (by simp) (by simp)`. Apply the tactic sequence `apply pullback.hom_ext <;> simp`. Use `⟨fun hu => ?_, ?_⟩` and prove the remaining obligations. Establish `hsq : IsPullback (pullback.lift (pullback.fst (u ≫ f) g ≫ u) (pullback.snd (u ≫ f) g) (by rw [Category.assoc, pullback.condition]) : pullback (u ≫ f) g ⟶ pullback f g) (pullback.fst (u ≫ f) g) (pullback.fst f g) u`.

Use `IsPullback.of_right (h₁₂ := pullback.snd f g) (h₂₂ := f) (v₁₃ := g) ?_ (by simp) (IsPullback.of_hasPullback f g).flip` and prove the remaining obligations. Rewrite using `[pullback.lift_snd]`. Conclude with `(IsPullback.of_hasPullback (u ≫ f) g).flip`. Conclude with `MorphismProperty.of_isPullback hsq.flip hu`. Rewrite using `[key, Scheme.Pullback.range_map]`.

Simplify using the standard rewrite rules.
-/
theorem lift_facts {X S Z Y : Scheme.{0}} (u : Y ⟶ X) (f : X ⟶ S) (g : Z ⟶ S) (fY : Y ⟶ S) (hf : u ≫ f = fY) :
    (IsOpenImmersion u → IsOpenImmersion (pullback.lift (pullback.fst fY g ≫ u) (pullback.snd fY g)
      (by rw [Category.assoc, hf, pullback.condition]) : pullback fY g ⟶ pullback f g)) ∧
    Set.range (pullback.lift (pullback.fst fY g ≫ u) (pullback.snd fY g)
      (by rw [Category.assoc, hf, pullback.condition]) : pullback fY g ⟶ pullback f g) =
      pullback.fst f g ⁻¹' Set.range u := by
  subst hf
  have key : (pullback.lift (pullback.fst (u ≫ f) g ≫ u) (pullback.snd (u ≫ f) g)
      (by rw [Category.assoc, pullback.condition]) : pullback (u ≫ f) g ⟶ pullback f g) =
      pullback.map (u ≫ f) g f g u (𝟙 Z) (𝟙 S) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp
  refine ⟨fun hu => ?_, ?_⟩
  · have hsq : IsPullback (pullback.lift (pullback.fst (u ≫ f) g ≫ u) (pullback.snd (u ≫ f) g)
        (by rw [Category.assoc, pullback.condition]) : pullback (u ≫ f) g ⟶ pullback f g)
        (pullback.fst (u ≫ f) g) (pullback.fst f g) u := by
      refine IsPullback.of_right (h₁₂ := pullback.snd f g) (h₂₂ := f) (v₁₃ := g) ?_ (by simp)
        (IsPullback.of_hasPullback f g).flip
      rw [pullback.lift_snd]
      exact (IsPullback.of_hasPullback (u ≫ f) g).flip
    exact MorphismProperty.of_isPullback hsq.flip hu
  · rw [key, Scheme.Pullback.range_map]
    simp

/- English proof (translation)
Take `⟨ho, hc, hd⟩` from `h`. Use `⟨fun s => (lift_facts (u s) f g (fY s) (hf s)).1 (ho s), fun x => ?_, fun s s' hss' => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `hc (pullback.fst f g x)`. Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[(lift_facts (u s) f g (fY s) (hf s)).2]`.

Conclude with `hs`. Rewrite using `[(lift_facts (u s) f g (fY s) (hf s)).2, (lift_facts (u s') f g (fY s') (hf s')).2]`. Conclude with `(hd s s' hss').preimage _`.
-/
theorem isSum_lift {X S Z : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (u : ∀ s, Y s ⟶ X) (f : X ⟶ S) (g : Z ⟶ S)
    (fY : ∀ s, Y s ⟶ S) (hf : ∀ s, u s ≫ f = fY s) (h : IsSum u) :
    IsSum (fun s => (pullback.lift (pullback.fst (fY s) g ≫ u s) (pullback.snd (fY s) g)
      (by rw [Category.assoc, hf, pullback.condition]) : pullback (fY s) g ⟶ pullback f g)) := by
  obtain ⟨ho, hc, hd⟩ := h
  refine ⟨fun s => (lift_facts (u s) f g (fY s) (hf s)).1 (ho s), fun x => ?_, fun s s' hss' => ?_⟩
  · obtain ⟨s, hs⟩ := hc (pullback.fst f g x)
    refine ⟨s, ?_⟩
    rw [(lift_facts (u s) f g (fY s) (hf s)).2]
    exact hs
  · rw [(lift_facts (u s) f g (fY s) (hf s)).2, (lift_facts (u s') f g (fY s') (hf s')).2]
    exact (hd s s' hss').preimage _

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev str (M : Model l K) : GlobalTheory.Et.geom (PadicAlgCl l) M.q ⟶ Spec (CommRingCat.of (PadicAlgCl l)) :=
  pullback.snd M.q (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))

/- English proof (translation)
The claim follows from `isSum_lift (fun a => Model.genMap (u a) (hu a)) M.q _ (fun a => (P a).q) (fun a => Model.genMap_q (u a) (hu a)) (isSum_lift u M.p _ (fun a => (P a).p) hu h)`.
-/
theorem isSum_geom {M : Model l K} {r : ℕ} {P : Fin r → Model l K} (u : ∀ a, (P a).X ⟶ M.X)
    (hu : ∀ a, u a ≫ M.p = (P a).p) (h : IsSum u) :
    IsSum (fun a => GlobalTheory.Et.geomMap (PadicAlgCl l) (P a).q (Model.genMap (u a) (hu a)) (Model.genMap_q (u a) (hu a))) :=
  isSum_lift (fun a => Model.genMap (u a) (hu a)) M.q _ (fun a => (P a).q) (fun a => Model.genMap_q (u a) (hu a))
    (isSum_lift u M.p _ (fun a => (P a).p) hu h)

/- English proof (translation)
Take `⟨N, i, hi, e⟩` from `h.1`. Use `ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (OK l K) N` as an intermediate fact. Rewrite using `[← e]`. Use `infer_instance`.
-/
theorem proper_p {M : Model l K} (h : M.Good) : IsProper M.p := by
  obtain ⟨N, i, hi, e⟩ := h.1
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (OK l K) N
  rw [← e]
  infer_instance

/- English proof (translation)
Use `proper_p h` as an intermediate fact. Use `infer_instance`.
-/
theorem proper_str {M : Model l K} (h : M.Good) : IsProper (str M) := by
  have := proper_p h
  infer_instance

/- English proof (translation)
Take `⟨ho, hcov, hd⟩` from `hj`. Use `ho s` as an intermediate fact. Use `proper_str h` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Establish `hcl : IsClosed (Set.range (j s))`.

Establish `: Set.range (j s) = (⋃ t ∈ ({s}ᶜ : Set (Fin r)), Set.range (j t))ᶜ`. Use extensionality with `x`. Simplify using `only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]`. Prove the components needed by the constructor for the conclusion. Introduce `hx t hts hxt`.

Conclude with `Set.disjoint_left.1 (hd s t (Ne.symm hts)) hx hxt`. Introduce `hx`. Take `⟨t, ht⟩` from `hcov x`. Distinguish the cases in `hts : t = s`. Conclude with `hts ▸ ht`.

Conclude with `absurd ht (hx t hts)`. Rewrite using `[this, isClosed_compl_iff]`. Conclude with `isOpen_biUnion fun t _ => (ho t).base_open.isOpen_range`. Establish `: IsClosedImmersion (j s)` using `.of_isPreimmersion _ hcl`. Use `infer_instance`.

Establish `h1 : SmoothOfRelativeDimension d M.q` using `hc.2`. Use `smoothOfRelativeDimension_isStableUnderBaseChange d` as an intermediate fact. Establish `h2 : SmoothOfRelativeDimension d (str M)` using `MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension d) _ _ h1`. Establish `h3` using `smoothOfRelativeDimension_comp (n := 0) (m := d) (j s) (str M)`. Rewrite `h3` using `[zero_add]`. Then use the resulting hypothesis.
-/
theorem comp_str {M : Model l K} (h : M.Good) {d : ℕ} (hc : M.Conn d) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (s : Fin r) :
    IsProper (j s ≫ str M) ∧ SmoothOfRelativeDimension d (j s ≫ str M) := by
  obtain ⟨ho, hcov, hd⟩ := hj
  have := ho s
  have := proper_str h
  constructor
  · have hcl : IsClosed (Set.range (j s)) := by
      have : Set.range (j s) = (⋃ t ∈ ({s}ᶜ : Set (Fin r)), Set.range (j t))ᶜ := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
        constructor
        · intro hx t hts hxt
          exact Set.disjoint_left.1 (hd s t (Ne.symm hts)) hx hxt
        · intro hx
          obtain ⟨t, ht⟩ := hcov x
          by_cases hts : t = s
          · exact hts ▸ ht
          · exact absurd ht (hx t hts)
      rw [this, isClosed_compl_iff]
      exact isOpen_biUnion fun t _ => (ho t).base_open.isOpen_range
    have : IsClosedImmersion (j s) := .of_isPreimmersion _ hcl
    infer_instance
  · have h1 : SmoothOfRelativeDimension d M.q := hc.2
    have := smoothOfRelativeDimension_isStableUnderBaseChange d
    have h2 : SmoothOfRelativeDimension d (str M) :=
      MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension d) _ _ h1
    have h3 := smoothOfRelativeDimension_comp (n := 0) (m := d) (j s) (str M)
    rwa [zero_add] at h3

/- English proof (translation)
Establish `h : IsUnit (q : Ω)` using `(Nat.cast_ne_zero.2 (NeZero.ne q)).isUnit`. Simplify using `using h.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ f.appTop).hom`.
-/
theorem unit_of_over {Ω : Type} [Field Ω] [CharZero Ω] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of Ω)) (q : ℕ)
    [NeZero q] : IsUnit (q : Γ(Y, ⊤)) := by
  have h : IsUnit (q : Ω) := (Nat.cast_ne_zero.2 (NeZero.ne q)).isUnit
  simpa using h.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ f.appTop).hom

/- English proof (translation)
Establish `hdeg : (Polynomial.cyclotomic q Ω).degree ≠ 0` using `(Polynomial.degree_cyclotomic_pos q Ω (NeZero.pos q)).ne'`. Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_root _ hdeg`. Establish `h0 : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `hζ`.

Conclude with `⟨GlobalTheory.EtC.Prim.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ f.appTop).hom ⟨ζ, (Nat.cast_ne_zero.2 (NeZero.ne q)).isUnit, h0⟩⟩`.
-/
theorem prim_of_over {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of Ω))
    (q : ℕ) [NeZero q] : Nonempty (GlobalTheory.EtC.Prim q Γ(Y, ⊤)) := by
  have hdeg : (Polynomial.cyclotomic q Ω).degree ≠ 0 := (Polynomial.degree_cyclotomic_pos q Ω (NeZero.pos q)).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  have h0 : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ
  exact ⟨GlobalTheory.EtC.Prim.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ f.appTop).hom
    ⟨ζ, (Nat.cast_ne_zero.2 (NeZero.ne q)).isUnit, h0⟩⟩

/- English proof (translation)
Introduce `U ⟨x⟩`. Express the relevant statement in the definitionally equal form `U ⟶ Y at x`. Simplify using `using h.map x.appTop.hom`.
-/
theorem inv_sch (q : ℕ) {Y : Scheme.{0}} (h : IsUnit (q : Γ(Y, ⊤))) : GlobalTheory.EtC.Inv q (GlobalTheory.EtC.sch.obj Y) := by
  intro U ⟨x⟩
  change U ⟶ Y at x
  simpa using h.map x.appTop.hom

end CrystallineSemistableComparison.AdicGeo
