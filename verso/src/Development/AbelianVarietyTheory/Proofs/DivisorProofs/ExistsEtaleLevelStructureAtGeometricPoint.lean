import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMoritaLatticeQuotientTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsAdditiveParametrizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev

/- English proof (translation)
Rewrite using `[← Spec.map_preimage x']`. Establish `: Flat (Spec.map (Spec.preimage x'))`. Rewrite using `[show Spec.preimage x' = CommRingCat.ofHom (Spec.preimage x').hom from rfl]`. Use `infer_instance`. Establish `: Surjective (Spec.map (Spec.preimage x'))` using `⟨fun _ => ⟨IsLocalRing.closedPoint k', Subsingleton.elim _ _⟩⟩`.

Conclude with `Flat.epi_of_flat_of_surjective _`.
-/
theorem epi_sp_field {k k' : Type} [Field k] [Field k'] (x' : Sp k' ⟶ Sp k) : Epi x' := by
  rw [← Spec.map_preimage x']
  have : Flat (Spec.map (Spec.preimage x')) := by
    rw [show Spec.preimage x' = CommRingCat.ofHom (Spec.preimage x').hom from rfl]; infer_instance
  have : Surjective (Spec.map (Spec.preimage x')) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint k', Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

/- English proof (translation)
Use `haveI := epi_sp_field x'`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `congrArg CommaMorphism.left h` as an intermediate fact. Simplify using `only [Over.comp_left, Over.homMk_left] at this`. Conclude with `(cancel_epi x').1 this`.
-/
theorem pt_ext_of_pullback {S : Scheme.{0}} {A : Over S} {k k' : Type} [Field k] [Field k'] (x : Sp k ⟶ S)
    (x' : Sp k' ⟶ Sp k) (g₁ g₂ : Over.mk x ⟶ A)
    (h : (Over.homMk x' rfl : Over.mk (x' ≫ x) ⟶ Over.mk x) ≫ g₁ =
      (Over.homMk x' rfl : Over.mk (x' ≫ x) ⟶ Over.mk x) ≫ g₂) : g₁ = g₂ := by
  haveI := epi_sp_field x'
  apply Over.OverMorphism.ext
  have := congrArg CommaMorphism.left h
  simp only [Over.comp_left, Over.homMk_left] at this
  exact (cancel_epi x').1 this

/- English proof (translation)
Introduce `p _ D R _ b N w0 r _hN hw S s o k _ _ x`. Establish `hw0 : w0 ≠ ⊥`. Introduce `h`. Establish `hp : (p : 𝓞 D.F) ∈ w0` using `hw.2.1`. Rewrite `hp` using `[h, Ideal.mem_bot]`.

Conclude with `(Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)`. Use `haveI : Finite (𝓞 D.F ⧸ w0 ^ r) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ hw0)`. Take `⟨f, fadd, fsm, finj, fsurj⟩` from `GlobalTheory.T.torsion_points_additive_parametrization p D R b N w0 r hw S s o k x`. Establish `hmul : ∀ (c : D.O) (g h : Over.mk x ⟶ o.A), (g * h) ≫ o.act.act c = (g ≫ o.act.act c) * (h ≫ o.act.act c)`. Introduce `c g h`.

Use `haveI := o.act.hom c`. Conclude with `MonObj.mul_comp _ _ _`. Take `⟨l, ladd, llin, lker, lsurj⟩` from `GlobalTheory.T.exists_morita_lattice_quotient_torsion p D w0 r hw.1 hw.2.1 (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun c g h => hmul c g h) (fun g => by simp only [o.act.one, Category.comp_id]) (fun b c g => by simp only [o.act.mul, Category.assoc]) (fun b c g => by simp …`. Establish `f0 : f 0 = 1`. Establish `h` using `fadd 0 0`.

Rewrite `h` using `[add_zero]`. Conclude with `mul_eq_left.mp h.symm`. Establish `tor : ∀ a, ∀ c ∈ w0 ^ r, f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1`. Introduce `a c hc`. Rewrite using `[← fsm, (Ideal.Quotient.eq_zero_iff_mem).2 hc, zero_smul, f0]`.

Use `⟨l, ladd, llin, fun y hy => (lker y).2 hy, ?_⟩` and prove the remaining obligations. Introduce `k' _ _ x'`. Use `⟨fun y hy => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Apply `(lker y).1` to reduce the goal to its premises. Apply `pt_ext_of_pullback x x'` to reduce the goal to its premises.

Rewrite using `[hy]`. Conclude with `(MonObj.comp_one _).symm`. Take `⟨f', -, -, -, f'surj⟩` from `GlobalTheory.T.torsion_points_additive_parametrization p D R b N w0 r hw S s o k' (x' ≫ x)`. Set `π : Over.mk (x' ≫ x) ⟶ Over.mk x` to `Over.homMk x' rfl`. Establish `tor' : ∀ a, ∀ c ∈ w0 ^ r, (π ≫ f a) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1`.

Introduce `a c hc`. Rewrite using `[Category.assoc, tor a c hc, MonObj.comp_one]`. Set `φ : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r)` to `fun a => (f'surj _ (tor' a)).choose`. Establish `hφ : ∀ a, f' (φ a) = π ≫ f a` using `fun a => (f'surj _ (tor' a)).choose_spec`. Establish `φinj : Function.Injective φ` using `fun a a' h => finj (pt_ext_of_pullback x x' _ _ (by rw [← hφ, ← hφ, h]))`.

Take `⟨a', rfl⟩` from `f'surj g hg`. Take `⟨a, ha⟩` from `(Finite.injective_iff_surjective.1 φinj) a'`. Take `⟨y, hy⟩` from `lsurj (f a) (tor a)`. Conclude with `⟨y, by rw [hy, ← ha, hφ]⟩`.
-/
theorem exists_etLevOver_geomPt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o w0 r l := by
  intro p _ D R _ b N w0 r _hN hw S s o k _ _ x
  have hw0 : w0 ≠ ⊥ := by
    intro h
    have hp : (p : 𝓞 D.F) ∈ w0 := hw.2.1
    rw [h, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)
  haveI : Finite (𝓞 D.F ⧸ w0 ^ r) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ hw0)
  obtain ⟨f, fadd, fsm, finj, fsurj⟩ := GlobalTheory.T.torsion_points_additive_parametrization p D R b N w0 r hw S s o k x
  have hmul : ∀ (c : D.O) (g h : Over.mk x ⟶ o.A), (g * h) ≫ o.act.act c = (g ≫ o.act.act c) * (h ≫ o.act.act c) := by
    intro c g h; haveI := o.act.hom c; exact MonObj.mul_comp _ _ _
  obtain ⟨l, ladd, llin, lker, lsurj⟩ := GlobalTheory.T.exists_morita_lattice_quotient_torsion p D w0 r hw.1 hw.2.1 (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun c g h => hmul c g h) (fun g => by simp only [o.act.one, Category.comp_id])
    (fun b c g => by simp only [o.act.mul, Category.assoc])
    (fun b c g => by simp only [o.act.add]; exact MonObj.comp_mul _ _ _) f fadd fsm finj fsurj
  have f0 : f 0 = 1 := by
    have h := fadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have tor : ∀ a, ∀ c ∈ w0 ^ r, f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro a c hc
    rw [← fsm, (Ideal.Quotient.eq_zero_iff_mem).2 hc, zero_smul, f0]
  refine ⟨l, ladd, llin, fun y hy => (lker y).2 hy, ?_⟩
  intro k' _ _ x'
  refine ⟨fun y hy => ?_, fun g hg => ?_⟩
  · apply (lker y).1
    apply pt_ext_of_pullback x x'
    rw [hy]
    exact (MonObj.comp_one _).symm
  · obtain ⟨f', -, -, -, f'surj⟩ := GlobalTheory.T.torsion_points_additive_parametrization p D R b N w0 r hw S s o k' (x' ≫ x)
    let π : Over.mk (x' ≫ x) ⟶ Over.mk x := Over.homMk x' rfl
    have tor' : ∀ a, ∀ c ∈ w0 ^ r, (π ≫ f a) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro a c hc
      rw [Category.assoc, tor a c hc, MonObj.comp_one]
    let φ : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      fun a => (f'surj _ (tor' a)).choose
    have hφ : ∀ a, f' (φ a) = π ≫ f a := fun a => (f'surj _ (tor' a)).choose_spec
    have φinj : Function.Injective φ := fun a a' h =>
      finj (pt_ext_of_pullback x x' _ _ (by rw [← hφ, ← hφ, h]))
    obtain ⟨a', rfl⟩ := f'surj g hg
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 φinj) a'
    obtain ⟨y, hy⟩ := lsurj (f a) (tor a)
    exact ⟨y, by rw [hy, ← ha, hφ]⟩
end GlobalTheory.UPel.HT.EtLev
