import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmoothQuot
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisLast

noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.SubEig

section Generic

variable {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module ℂ U]

def cyc (ρ : Representation ℂ G U) (u : U) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g : G => ρ g u)
  apply_mem_toSubmodule g v hv := by
    have hle : Submodule.span ℂ (Set.range fun g : G => ρ g u) ≤
        (Submodule.span ℂ (Set.range fun g : G => ρ g u)).comap (ρ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      refine Submodule.subset_span ⟨g * h, ?_⟩
      simp [map_mul]
    exact hle hv

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨1, by simp⟩`.
-/
theorem mem_cyc (ρ : Representation ℂ G U) (u : U) : u ∈ (cyc ρ u).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

/- English proof (translation)
Establish `hbot : (⊥ : Subrepresentation ρ) ∈ {T : Subrepresentation ρ | u ∉ T.toSubmodule}` using `by show u ∉ (⊥ : Submodule ℂ U)`. Simplify using `using hu`. Establish `hz : ∀ c ⊆ {T : Subrepresentation ρ | u ∉ T.toSubmodule}, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ {T : Subrepresentation ρ | u ∉ T.toSubmodule}, ∀ z ∈ c, z ≤ ub`. Introduce `c hc hchain y hy`. Establish `hne : (Subrepresentation.toSubmodule '' c).Nonempty` using `⟨_, y, hy, rfl⟩`.

Establish `hdir : DirectedOn (· ≤ ·) (Subrepresentation.toSubmodule '' c)`. Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩`. Break down `hchain.total ha hb with h | h` into its components or cases. Conclude with `⟨_, ⟨b, hb, rfl⟩, h, le_rfl⟩`. Conclude with `⟨_, ⟨a, ha, rfl⟩, le_rfl, h⟩`.

Establish `hmem : ∀ x, x ∈ sSup (Subrepresentation.toSubmodule '' c) ↔ ∃ a ∈ c, x ∈ Subrepresentation.toSubmodule a`. Introduce `x`. Rewrite using `[Submodule.mem_sSup_of_directed hne hdir]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨a, ha, rfl⟩, hx⟩`.

Conclude with `⟨a, ha, hx⟩`. Introduce and unpack `⟨a, ha, hx⟩`. Conclude with `⟨_, ⟨a, ha, rfl⟩, hx⟩`. Use `⟨⟨sSup (Subrepresentation.toSubmodule '' c), ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `g v hv`.

Take `⟨a, ha, hx⟩` from `(hmem v).1 hv`. Conclude with `(hmem _).2 ⟨a, ha, a.apply_mem_toSubmodule g hx⟩`. Introduce `h`. Take `⟨a, ha, hx⟩` from `(hmem u).1 h`. Conclude with `hc ha hx`.

Introduce `z hz x hx`. Conclude with `(hmem x).2 ⟨z, hz, hx⟩`. Take `⟨T, -, hT⟩` from `zorn_le_nonempty₀ {T : Subrepresentation ρ | u ∉ T.toSubmodule} hz ⊥ hbot`. Conclude with `⟨T, hT.prop, fun T' hle hu' => le_antisymm (hT.le_of_ge hu' hle) hle⟩`.
-/
theorem exists_max_avoid (ρ : Representation ℂ G U) {u : U} (hu : u ≠ 0) :
    ∃ T : Subrepresentation ρ, u ∉ T.toSubmodule ∧
      ∀ T' : Subrepresentation ρ, T ≤ T' → u ∉ T'.toSubmodule → T' = T := by
  have hbot : (⊥ : Subrepresentation ρ) ∈ {T : Subrepresentation ρ | u ∉ T.toSubmodule} := by
    show u ∉ (⊥ : Submodule ℂ U)
    simpa using hu
  have hz : ∀ c ⊆ {T : Subrepresentation ρ | u ∉ T.toSubmodule}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {T : Subrepresentation ρ | u ∉ T.toSubmodule}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    have hne : (Subrepresentation.toSubmodule '' c).Nonempty := ⟨_, y, hy, rfl⟩
    have hdir : DirectedOn (· ≤ ·) (Subrepresentation.toSubmodule '' c) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rcases hchain.total ha hb with h | h
      · exact ⟨_, ⟨b, hb, rfl⟩, h, le_rfl⟩
      · exact ⟨_, ⟨a, ha, rfl⟩, le_rfl, h⟩
    have hmem : ∀ x, x ∈ sSup (Subrepresentation.toSubmodule '' c) ↔
        ∃ a ∈ c, x ∈ Subrepresentation.toSubmodule a := by
      intro x
      rw [Submodule.mem_sSup_of_directed hne hdir]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, hx⟩
        exact ⟨a, ha, hx⟩
      · rintro ⟨a, ha, hx⟩
        exact ⟨_, ⟨a, ha, rfl⟩, hx⟩
    refine ⟨⟨sSup (Subrepresentation.toSubmodule '' c), ?_⟩, ?_, ?_⟩
    · intro g v hv
      obtain ⟨a, ha, hx⟩ := (hmem v).1 hv
      exact (hmem _).2 ⟨a, ha, a.apply_mem_toSubmodule g hx⟩
    · intro h
      obtain ⟨a, ha, hx⟩ := (hmem u).1 h
      exact hc ha hx
    · intro z hz x hx
      exact (hmem x).2 ⟨z, hz, hx⟩
  obtain ⟨T, -, hT⟩ := zorn_le_nonempty₀ {T : Subrepresentation ρ | u ∉ T.toSubmodule} hz ⊥ hbot
  exact ⟨T, hT.prop, fun T' hle hu' => le_antisymm (hT.le_of_ge hu' hle) hle⟩

/- English proof (translation)
Establish `hle : (cyc ρ u).toSubmodule ≤ R.toSubmodule.map (cyc ρ u).toSubmodule.subtype`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨_, R.apply_mem_toSubmodule g hR, rfl⟩`. Use `le_antisymm le_top fun x _ => ?_` and prove the remaining obligations.

Take `⟨y, hy, hyx⟩` from `hle x.2`. Establish `: y = x` using `Subtype.ext hyx`. Conclude with `this ▸ hy`.
-/
theorem cyc_gen (ρ : Representation ℂ G U) (u : U)
    (R : Subrepresentation (cyc ρ u).toRepresentation)
    (hR : (⟨u, mem_cyc ρ u⟩ : (cyc ρ u).toSubmodule) ∈ R.toSubmodule) : R = ⊤ := by
  have hle : (cyc ρ u).toSubmodule ≤ R.toSubmodule.map (cyc ρ u).toSubmodule.subtype := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨_, R.apply_mem_toSubmodule g hR, rfl⟩
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

/- English proof (translation)
Establish `hne : (Submodule.Quotient.mk u : U ⧸ T.toSubmodule) ≠ 0`. Rewrite using `[Ne, Submodule.Quotient.mk_eq_zero]` and apply the resulting hypothesis. Establish `hnt : Nontrivial (Subrepresentation (ρ.quotient T.toSubmodule hst))`. Use `⟨⊥, ⊤, fun h => hne ?_⟩` and prove the remaining obligations. Establish `h1 : (Submodule.Quotient.mk u : U ⧸ T.toSubmodule) ∈ (⊤ : Subrepresentation (ρ.quotient T.toSubmodule hst)).toSubmodule` using `trivial`.

Rewrite `h1` using `[← h]`. Conclude with `(Submodule.mem_bot ℂ).1 h1`. Use `⟨fun R => ?_⟩` and prove the remaining obligations. Set `T' : Subrepresentation ρ` to `⟨R.toSubmodule.comap T.toSubmodule.mkQ, by`. Introduce `g v hv`.

Use `R.apply_mem_toSubmodule g hv` as an intermediate fact. Conclude with `this⟩`. Establish `hle : T ≤ T'`. Introduce `x hx`. Use `show T.toSubmodule.mkQ x ∈ R.toSubmodule`.

Establish `h0 : T.toSubmodule.mkQ x = 0` using `(Submodule.Quotient.mk_eq_zero _).2 hx`. Rewrite using `[h0]`. Conclude with `R.toSubmodule.zero_mem`. Distinguish the cases in `huT : u ∈ T'.toSubmodule`. Use `right`.

Establish `hT'` using `hgen T' huT`. Use `le_antisymm le_top fun x _ => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `: y ∈ T'.toSubmodule` using `by rw [hT']; trivial`. Conclude with `this`.

Use `left`. Establish `hT'` using `hmax T' hle huT`. Use `le_antisymm (fun x hx => ?_) bot_le` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `hy : y ∈ T'.toSubmodule` using `hx`.

Rewrite `hy` using `[hT']`. Establish `: (Submodule.Quotient.mk y : U ⧸ T.toSubmodule) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]` and apply the resulting hypothesis. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.
-/
theorem quot_irred (ρ : Representation ℂ G U) (T : Subrepresentation ρ) {u : U}
    (hu : u ∉ T.toSubmodule)
    (hmax : ∀ T' : Subrepresentation ρ, T ≤ T' → u ∉ T'.toSubmodule → T' = T)
    (hgen : ∀ R : Subrepresentation ρ, u ∈ R.toSubmodule → R = ⊤)
    (hst : ∀ g, T.toSubmodule ≤ T.toSubmodule.comap (ρ g)) :
    (ρ.quotient T.toSubmodule hst).IsIrreducible := by
  have hne : (Submodule.Quotient.mk u : U ⧸ T.toSubmodule) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hnt : Nontrivial (Subrepresentation (ρ.quotient T.toSubmodule hst)) := by
    refine ⟨⊥, ⊤, fun h => hne ?_⟩
    have h1 : (Submodule.Quotient.mk u : U ⧸ T.toSubmodule) ∈
        (⊤ : Subrepresentation (ρ.quotient T.toSubmodule hst)).toSubmodule := trivial
    rw [← h] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  refine ⟨fun R => ?_⟩
  let T' : Subrepresentation ρ := ⟨R.toSubmodule.comap T.toSubmodule.mkQ, by
    intro g v hv
    have := R.apply_mem_toSubmodule g hv
    exact this⟩
  have hle : T ≤ T' := by
    intro x hx
    show T.toSubmodule.mkQ x ∈ R.toSubmodule
    have h0 : T.toSubmodule.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero _).2 hx
    rw [h0]
    exact R.toSubmodule.zero_mem
  by_cases huT : u ∈ T'.toSubmodule
  · right
    have hT' := hgen T' huT
    refine le_antisymm le_top fun x _ => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have : y ∈ T'.toSubmodule := by rw [hT']; trivial
    exact this
  · left
    have hT' := hmax T' hle huT
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hy : y ∈ T'.toSubmodule := hx
    rw [hT'] at hy
    have : (Submodule.Quotient.mk y : U ⧸ T.toSubmodule) = 0 := by
      rwa [Submodule.Quotient.mk_eq_zero]
    rw [this]
    exact Submodule.zero_mem _

def mkI (ρ : Representation ℂ G U) (T : Submodule ℂ U) (hst : ∀ g, T ≤ T.comap (ρ g)) :
    Representation.IntertwiningMap ρ (ρ.quotient T hst) where
  toLinearMap := T.mkQ
  isIntertwining' g := by
    ext v
    rfl

def inclI {ρ : Representation ℂ G U} (S : Subrepresentation ρ) :
    Representation.IntertwiningMap S.toRepresentation ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def stab (ρ : Representation ℂ G U) (v : U) : Subgroup G :=
  _root_.UpperTheory.Reformulated.B.RepresentationStabilizer.stab ρ v

/- English proof (translation)
Introduce `v`. Establish `: {g : G | S.toRepresentation g v = v} = {g : G | ρ g (v : U) = v}`. Use extensionality with `g`. Conclude with `Subtype.ext_iff`. Rewrite using `[this]`.

Conclude with `hρ _`.
-/
theorem smooth_sub {ρ : Representation ℂ G U} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := by
  intro v
  have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g (v : U) = v} := by
    ext g
    exact Subtype.ext_iff
  rw [this]
  exact hρ _

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Gwb5.smooth_quot hρ T hst`.
-/
theorem smooth_quot {ρ : Representation ℂ G U} (hρ : IsSmooth ρ) (T : Submodule ℂ U)
    (hst : ∀ g, T ≤ T.comap (ρ g)) : IsSmooth (ρ.quotient T hst) :=
  _root_.UpperTheory.Reformulated.B.Gwb5.smooth_quot hρ T hst

end Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

end GlobalTheory.CompanionTheory.SubEig
