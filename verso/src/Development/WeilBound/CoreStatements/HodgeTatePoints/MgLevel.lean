import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Mg

abbrev extPt {X : Scheme.{0}} {k K : Type} [Field k] [Field K] (i : k →+* K) (x : Sp k ⟶ X) :
    Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl

/- English proof (translation)
Establish `: Surjective (spMap i)` using `⟨fun z => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩`. Conclude with `Flat.epi_of_flat_of_surjective _`.
-/
theorem epi_spMap {k K : Type} [Field k] [Field K] (i : k →+* K) : Epi (spMap i) := by
  have : Surjective (spMap i) :=
    ⟨fun z => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

/- English proof (translation)
Use `epi_spMap i` as an intermediate fact. Establish `h' : spMap i ≫ a.left = spMap i ≫ b.left` using `congrArg (fun q => q.left) h`. Conclude with `Over.OverMorphism.ext ((cancel_epi (spMap i)).1 h')`.
-/
theorem extPt_inj {X : Scheme.{0}} {k K : Type} [Field k] [Field K] (i : k →+* K) (x : Sp k ⟶ X) {G : Over X}
    {a b : Over.mk x ⟶ G} (h : extPt i x ≫ a = extPt i x ≫ b) : a = b := by
  have := epi_spMap i
  have h' : spMap i ≫ a.left = spMap i ≫ b.left := congrArg (fun q => q.left) h
  exact Over.OverMorphism.ext ((cancel_epi (spMap i)).1 h')

/- English proof (translation)
Use `show Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {X : Scheme.{0}}
  {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ} {z : Ωˣ} {ev : D.La → (Over.mk ξ ⟶ t.G)}

/- English proof (translation)
Take `⟨I, h1, h2⟩` from `h k i`. Conclude with `⟨I, Units.ext h1, fun a => Over.OverMorphism.ext (h2 a)⟩`.
-/
theorem full_iso (h : IsFullLevelAt D t ξ N z ev) (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) :
    ∃ I : TateIsoAt D t (spMap i ≫ ξ), I.ζ N = Units.map i.toMonoidHom z ∧ ∀ a, I.ev N a = extPt i ξ ≫ ev a := by
  obtain ⟨I, h1, h2⟩ := h k i
  exact ⟨I, Units.ext h1, fun a => Over.OverMorphism.ext (h2 a)⟩

/- English proof (translation)
Set `j : k →+* AlgebraicClosure k` to `algebraMap _ _`. Take `⟨I, -, h2⟩` from `h (AlgebraicClosure k) (j.comp i)`. Set `u : Over.mk (spMap (j.comp i) ≫ ξ) ⟶ Over.mk (spMap i ≫ ξ)` to `Over.homMk (spMap j) (by simp [spMap_comp])`. Take `⟨a, ha⟩` from `(I.onto N hN (u ≫ g)).1 (by rw [← MonObj.comp_pow, hg, MonObj.comp_one])`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Use `epi_spMap j` as an intermediate fact. Establish `e : spMap j ≫ g.left = (I.ev N a).left` using `by rw [ha]; rfl`. Rewrite using `[← cancel_epi (spMap j), e, h2, spMap_comp, Category.assoc]`.
-/
theorem full_desc (hN : 0 < N) (h : IsFullLevelAt D t ξ N z ev) (k : Type) [Field k] (i : Ω →+* k)
    (g : Over.mk (spMap i ≫ ξ) ⟶ t.G) (hg : g ^ N = 1) : ∃ a, g.left = spMap i ≫ (ev a).left := by
  let j : k →+* AlgebraicClosure k := algebraMap _ _
  obtain ⟨I, -, h2⟩ := h (AlgebraicClosure k) (j.comp i)
  let u : Over.mk (spMap (j.comp i) ≫ ξ) ⟶ Over.mk (spMap i ≫ ξ) :=
    Over.homMk (spMap j) (by simp [spMap_comp])
  obtain ⟨a, ha⟩ := (I.onto N hN (u ≫ g)).1 (by rw [← MonObj.comp_pow, hg, MonObj.comp_one])
  refine ⟨a, ?_⟩
  have := epi_spMap j
  have e : spMap j ≫ g.left = (I.ev N a).left := by rw [ha]; rfl
  rw [← cancel_epi (spMap j), e, h2, spMap_comp, Category.assoc]

/- English proof (translation)
Introduce `E _ _ _ H D X t Ω _ ξ n m hn hm z ev h k _ _ i`. Take `⟨I, h1, h2⟩` from `full_iso h k i`. Use `⟨I, ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← I.ζ_pow n m hn hm, h1, ← map_pow]`. Both sides reduce to the same expression.

Rewrite using `[← I.tower n m hn hm, h2, ← MonObj.comp_pow]`. Both sides reduce to the same expression.
-/
theorem level_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (n m : ℕ), 0 < n → 0 < m → ∀ (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ (n * m) z ev → IsFullLevelAt D t ξ n (z ^ m) fun a => ev a ^ m := by
  intro E _ _ _ H D X t Ω _ ξ n m hn hm z ev h k _ _ i
  obtain ⟨I, h1, h2⟩ := full_iso h k i
  refine ⟨I, ?_, fun a => ?_⟩
  · rw [← I.ζ_pow n m hn hm, h1, ← map_pow]
    rfl
  · rw [← I.tower n m hn hm, h2, ← MonObj.comp_pow]
    rfl

/- English proof (translation)
Introduce `E _ _ _ H D X t Ω _ ξ N hN z ev h`. Set `j : Ω →+* AlgebraicClosure Ω` to `algebraMap _ _`. Take `⟨I, h1, h2⟩` from `full_iso h (AlgebraicClosure Ω) j`. Use `⟨?_, fun a b => ?_, fun r a => ?_, fun a => ?_, fun g => ?_, fun k _ i g hg => ?_, fun k _ _ i a b g g' hg hg' => ?_⟩` and prove the remaining obligations. Use `IsPrimitiveRoot.of_map_of_injective (f := Units.map j.toMonoidHom) ?_ (Units.map_injective j.injective)` and prove the remaining obligations.

Rewrite using `[← h1]`. Conclude with `I.ζ_prim N hN`. Apply `extPt_inj j` to reduce the goal to its premises. Rewrite using `[MonObj.comp_mul, ← h2, ← h2, ← h2, I.add]`. Apply `extPt_inj j` to reduce the goal to its premises.

Rewrite using `[← h2, I.lin, h2, Category.assoc]`. Rewrite using `[← I.ker N hN a, h2]`. Conclude with `⟨fun e => by rw [e, MonObj.comp_one], fun e => extPt_inj j ξ (by rw [e, MonObj.comp_one])⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hg`.

Take `⟨a, ha⟩` from `(I.onto N hN (extPt j ξ ≫ g)).1 (by rw [← MonObj.comp_pow, hg, MonObj.comp_one])`. Conclude with `⟨a, extPt_inj j ξ (by rw [← h2, ha])⟩`. Introduce and unpack `⟨a, rfl⟩`. Apply `extPt_inj j` to reduce the goal to its premises. Rewrite using `[MonObj.comp_pow, ← h2, MonObj.comp_one]`.

Conclude with `(I.onto N hN _).2 ⟨a, rfl⟩`. Take `⟨a, ha⟩` from `full_desc hN h k i g hg`. Conclude with `⟨ev a, ha⟩`. Take `⟨J, e1, e2⟩` from `full_iso h k i`. Establish `hg1 : g = J.ev N a` using `by rw [e2]; exact Over.OverMorphism.ext hg`.

Establish `hg2 : g' = J.ev N b` using `by rw [e2]; exact Over.OverMorphism.ext hg'`. Rewrite using `[hg1, hg2, ← e1]`. Conclude with `J.isom N hN a b`.
-/
theorem level_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ), 0 < N → ∀ (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → IsPrimitiveRoot z N ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (r : 𝓞 E) a, ev (r • a) = ev a ≫ t.act.act r) ∧ (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ g : Over.mk ξ ⟶ t.G, g ^ N = 1 ↔ ∃ a, ev a = g) ∧ FullTorsion t.G ξ N ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (a b : D.La) (g g' : Over.mk (spMap i ≫ ξ) ⟶ t.G), g.left = spMap i ≫ (ev a).left → g'.left = spMap i ≫ (ev b).left → Out.WeilIs t.G t.PP.L N g g' (unitOn (Units.map i.toMonoidHom z ^ D.EF a b)) := by
  intro E _ _ _ H D X t Ω _ ξ N hN z ev h
  let j : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  obtain ⟨I, h1, h2⟩ := full_iso h (AlgebraicClosure Ω) j
  refine ⟨?_, fun a b => ?_, fun r a => ?_, fun a => ?_, fun g => ?_, fun k _ i g hg => ?_,
    fun k _ _ i a b g g' hg hg' => ?_⟩
  · refine IsPrimitiveRoot.of_map_of_injective (f := Units.map j.toMonoidHom) ?_ (Units.map_injective j.injective)
    rw [← h1]
    exact I.ζ_prim N hN
  · apply extPt_inj j
    rw [MonObj.comp_mul, ← h2, ← h2, ← h2, I.add]
  · apply extPt_inj j
    rw [← h2, I.lin, h2, Category.assoc]
  · rw [← I.ker N hN a, h2]
    exact ⟨fun e => by rw [e, MonObj.comp_one], fun e => extPt_inj j ξ (by rw [e, MonObj.comp_one])⟩
  · constructor
    · intro hg
      obtain ⟨a, ha⟩ := (I.onto N hN (extPt j ξ ≫ g)).1 (by rw [← MonObj.comp_pow, hg, MonObj.comp_one])
      exact ⟨a, extPt_inj j ξ (by rw [← h2, ha])⟩
    · rintro ⟨a, rfl⟩
      apply extPt_inj j
      rw [MonObj.comp_pow, ← h2, MonObj.comp_one]
      exact (I.onto N hN _).2 ⟨a, rfl⟩
  · obtain ⟨a, ha⟩ := full_desc hN h k i g hg
    exact ⟨ev a, ha⟩
  · obtain ⟨J, e1, e2⟩ := full_iso h k i
    have hg1 : g = J.ev N a := by rw [e2]; exact Over.OverMorphism.ext hg
    have hg2 : g' = J.ev N b := by rw [e2]; exact Over.OverMorphism.ext hg'
    rw [hg1, hg2, ← e1]
    exact J.isom N hN a b

/- English proof (translation)
Use `D.fin` as an intermediate fact. Use `⟨GlobalTheory.datum_free_int D, Module.Finite.trans (𝓞 E) D.La, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.finrank_int_eq_mul_of_finite (O := 𝓞 E), D.rank, RingOfIntegers.rank]`.
-/
theorem finrank_La (D : Datum H) : Module.Free ℤ D.La ∧ Module.Finite ℤ D.La ∧
    Module.finrank ℤ D.La = Module.finrank ℚ E * (D.p + D.q) := by
  have := D.fin
  refine ⟨GlobalTheory.datum_free_int D, Module.Finite.trans (𝓞 E) D.La, ?_⟩
  rw [GlobalTheory.finrank_int_eq_mul_of_finite (O := 𝓞 E), D.rank, RingOfIntegers.rank]

/- English proof (translation)
Introduce `E _ _ _ H D X t Ω _ ξ N hN z ev h`. Take `⟨-, hadd, -, hker, honto, -, -⟩` from `level_props E H D X t Ω ξ N hN z ev h`. Set `R` to `LinearMap.range (N • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))`. Establish `hR : ∀ a, a ∈ R ↔ ∃ b, a = N • b` using `fun a => ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩`. Establish `hq : ∀ a b, ev a = ev b ↔ (Submodule.Quotient.mk a : D.La ⧸ R) = Submodule.Quotient.mk b` using `fun a b => by`.

Establish `e : ev a = ev (a - b) * ev b` using `by rw [← hadd, sub_add_cancel]`. Rewrite using `[Submodule.Quotient.eq, e, mul_eq_right, hker, hR]`. Use `choose s hs using Submodule.Quotient.mk_surjective R`. Establish `hs' : ∀ a, ev (s (Submodule.Quotient.mk a)) = ev a` using `fun a => (hq _ _).2 (hs _)`. Set `τ : Multiplicative (D.La ⧸ R) →* (Over.mk ξ ⟶ t.G)` to `MonoidHom.mk' (fun y => ev (s y.toAdd)) (fun y y' => by`.

Rewrite using `[← hadd, hq, hs, Submodule.Quotient.mk_add, hs, hs, toAdd_mul])`. Use `⟨τ, fun y y' e => ?_, fun a => hs' a, fun y => (honto _).2 ⟨_, rfl⟩, fun k _ i g hg => ?_, ?_⟩` and prove the remaining obligations. Establish `e'` using `(hq _ _).1 e`. Rewrite `e'` using `[hs, hs]`. Conclude with `Multiplicative.toAdd.injective e'`.

Take `⟨a, ha⟩` from `full_desc hN h k i g hg`. Use `⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), ?_⟩` and prove the remaining obligations. Rewrite using `[ha, ← hs' a]`. Both sides reduce to the same expression. Take `⟨h1, h2, h3⟩` from `finrank_La D`.

Rewrite using `[← h3, ← AddSubgroup.index_range_nsmul D.La N]`. Establish `e : R.toAddSubgroup = (nsmulAddMonoidHom (α` using `D.La) N).range := by`. Use extensionality with `a`. Conclude with `⟨fun ⟨b, hb⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb⟩⟩`. Rewrite using `[← e]`.

Both sides reduce to the same expression.
-/
theorem level_tau : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ), 0 < N → ∀ (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → ∃ τ : Multiplicative (D.La ⧸ LinearMap.range (N • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))) →* (Over.mk ξ ⟶ t.G), Function.Injective τ ∧ (∀ a : D.La, τ (Multiplicative.ofAdd (Submodule.Quotient.mk a)) = ev a) ∧ (∀ s, τ s ^ N = 1) ∧ (∀ (k : Type) [Field k] (i : Ω →+* k) (g : Over.mk (spMap i ≫ ξ) ⟶ t.G), g ^ N = 1 → ∃ s, g.left = spMap i ≫ (τ s).left) ∧ Nat.card (D.La ⧸ LinearMap.range (N • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))) = N ^ (Module.finrank ℚ E * (D.p + D.q)) := by
  intro E _ _ _ H D X t Ω _ ξ N hN z ev h
  obtain ⟨-, hadd, -, hker, honto, -, -⟩ := level_props E H D X t Ω ξ N hN z ev h
  let R := LinearMap.range (N • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))
  have hR : ∀ a, a ∈ R ↔ ∃ b, a = N • b := fun a => ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hq : ∀ a b, ev a = ev b ↔ (Submodule.Quotient.mk a : D.La ⧸ R) = Submodule.Quotient.mk b := fun a b => by
    have e : ev a = ev (a - b) * ev b := by rw [← hadd, sub_add_cancel]
    rw [Submodule.Quotient.eq, e, mul_eq_right, hker, hR]
  choose s hs using Submodule.Quotient.mk_surjective R
  have hs' : ∀ a, ev (s (Submodule.Quotient.mk a)) = ev a := fun a => (hq _ _).2 (hs _)
  let τ : Multiplicative (D.La ⧸ R) →* (Over.mk ξ ⟶ t.G) := MonoidHom.mk' (fun y => ev (s y.toAdd)) (fun y y' => by
    rw [← hadd, hq, hs, Submodule.Quotient.mk_add, hs, hs, toAdd_mul])
  refine ⟨τ, fun y y' e => ?_, fun a => hs' a, fun y => (honto _).2 ⟨_, rfl⟩, fun k _ i g hg => ?_, ?_⟩
  · have e' := (hq _ _).1 e
    rw [hs, hs] at e'
    exact Multiplicative.toAdd.injective e'
  · obtain ⟨a, ha⟩ := full_desc hN h k i g hg
    refine ⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), ?_⟩
    rw [ha, ← hs' a]
    rfl
  · obtain ⟨h1, h2, h3⟩ := finrank_La D
    rw [← h3, ← AddSubgroup.index_range_nsmul D.La N]
    have e : R.toAddSubgroup = (nsmulAddMonoidHom (α := D.La) N).range := by
      ext a
      exact ⟨fun ⟨b, hb⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb⟩⟩
    rw [← e]
    rfl

end PositivityTheory.HtPt.Mg
