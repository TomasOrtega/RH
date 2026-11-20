import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.GenFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj in

/- English proof (translation)
Take `⟨hex, hinj, -, -, hlie, heig⟩` from `_root_.GlobalTheory.CM.integral_tangent_coordinates K P F`. Establish `hcoord : ∀ {u c c'}, F.IsCoord u c → F.IsCoord u c' → c = c'` using `fun h h' => (hex _ h.1).unique h h'`. Establish `hdiff : ∀ a, ∃! M, F.IsDiffOf F (act.act a) M` using `fun a => (_root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P F (act.act a) (act.hom a)).1`. Use `choose R hR using fun a => (hdiff a).exists`. Establish `huniq : ∀ a M, F.IsDiffOf F (act.act a) M → R a = M` using `fun a M h => (hdiff a).unique (hR a) h`.

Establish `hone : R 1 = 1` using `huniq 1 1 (by`. Introduce `u c h`. Simplify `h)` using `[act.one]`. Establish `hmul : ∀ a b, R (a * b) = R a * R b` using `fun a b => by`. Rewrite using `[mul_comm a b]`.

Use `huniq _ _ ?_` and prove the remaining obligations. Introduce `u c h`. Rewrite using `[act.mul, ← Category.assoc]`. Conclude with `hR a _ _ (hR b u c h)`. Establish `hadd : ∀ a b, R (a + b) = R a + R b` using `fun a b => by`.

Use `huniq _ _ ?_` and prove the remaining obligations. Introduce `u c h`. Rewrite using `[act.add, comp_mul]`. Conclude with `_root_.GlobalTheory.CM.IntCoord.isCoord_mul F (hR a u c h) (hR b u c h)`. Establish `hspan : Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨φ, hφ0, hle⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hφ0 (LinearMap.ext h)`. Establish `hM : F.IsDiffOf F (act.act 1) (1 + φ.smulRight x)`. Introduce `u c h`. Establish `hφc : φ c = 0` using `LinearMap.mem_ker.1 (hle (Submodule.subset_span ((hlie c).2 ⟨u, h⟩)))`. Simplify `h` using `[act.one, hφc]`.

Establish `h1` using `LinearMap.congr_fun (hone.symm.trans (huniq 1 _ hM)) x`. Simplify using `at h1`. Break down `h1 with h1 | h1` into its components or cases. Conclude with `hx h1`. Conclude with `hx (by simp [h1])`.

Establish `hlat : ∀ τ : O →+* 𝓞 K, ∀ c, c ∈ F.eigLat act τ ↔ c ∈ F.lieLat ∧ ∀ a, R a c = τ a • c`. Introduce `τ c`. Rewrite using `[heig O act τ c, hlie c]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hcomb⟩`.

Conclude with `⟨⟨u, hu⟩, fun a => hcoord (hR a u c hu) (_root_.GlobalTheory.CM.IntCoord.isCoord_smul F hu (hcomb a))⟩`. Introduce and unpack `⟨⟨u, hu⟩, hc⟩`. Use `⟨u, hu, fun a => ?_⟩` and prove the remaining obligations. Establish `hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb ![τ a] ![u] (_root_.GlobalTheory.CM.IntCoord.sc (τ a) ≫ u)` using `(_root_.GlobalTheory.CM.IntCoord.isLieComb_one_iff _ _ _).2 rfl`. Establish `he` using `hinj _ _ _ (hR a u c hu) (by rw [hc a]; exact _root_.GlobalTheory.CM.IntCoord.isCoord_smul F hu hs)`.

Rewrite using `[he]`. Conclude with `hs`. Use `⟨RingHom.mk' ⟨⟨R, hone⟩, hmul⟩ hadd, fun a => hR a, fun τ c => ⟨hlat τ c, ?_⟩⟩` and prove the remaining obligations. Use `show _ ↔ ∀ a, R a c = τ a • c`. Prove the components needed by the constructor for the conclusion.

Introduce `hc`. Use `Submodule.span_induction (p := fun c _ => ∀ a, R a c = τ a • c) ?_ ?_ ?_ ?_ hc` and prove the remaining obligations. Conclude with `fun x hx a => ((hlat τ x).1 hx).2 a`. Introduce `a`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy a`. Rewrite using `[map_add, hx, hy, smul_add]`. Introduce `k x _ hx a`. Rewrite using `[map_smul, hx, smul_comm]`. Introduce `hc`.

Establish `hcspan : c ∈ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K))`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`. Take `⟨y, hy, z, rfl⟩` from `(IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 K))).1 hcspan`. Rewrite `hy` using `[Submodule.span_eq]`.

Establish `hzy : (z : 𝓞 K) • (IsLocalization.mk' K (1 : 𝓞 K) z • y) = y`. Rewrite using `[← smul_assoc, Algebra.smul_def (z : 𝓞 K) (IsLocalization.mk' K (1 : 𝓞 K) z), IsLocalization.mk'_spec', map_one, one_smul]`. Establish `hyeig : ∀ a, R a y = τ a • y` using `fun a => by`. Rewrite using `[← hzy, LinearMap.map_smul_of_tower, hc a, smul_comm]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ((hlat τ y).2 ⟨hy, hyeig⟩))`.
-/
theorem _root_.GlobalTheory.CM.GenFib.exists_lieRep_eigLat (K : Type) [Field K]
    [NumberField K] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (𝓞 K))) (F : _root_.GlobalTheory.CM.GenFib P) (O : Type)
    [CommRing O] (act : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O P.A) :
    ∃ r : O →+* Module.End K (Fin F.P₀.g → K),
      (∀ a, F.IsDiffOf F (act.act a) (r a)) ∧
      ∀ (τ : O →+* 𝓞 K) c, (c ∈ F.eigLat act τ ↔
          c ∈ F.lieLat ∧ ∀ a, r a c = τ a • c) ∧
        (c ∈ Submodule.span K (F.eigLat act τ :
            Set (Fin F.P₀.g → K)) ↔ ∀ a, r a c = τ a • c) := by
  obtain ⟨hex, hinj, -, -, hlie, heig⟩ := _root_.GlobalTheory.CM.integral_tangent_coordinates K P F
  have hcoord : ∀ {u c c'}, F.IsCoord u c → F.IsCoord u c' → c = c' := fun h h' =>
    (hex _ h.1).unique h h'
  have hdiff : ∀ a, ∃! M, F.IsDiffOf F (act.act a) M := fun a =>
    (_root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P F (act.act a) (act.hom a)).1
  choose R hR using fun a => (hdiff a).exists
  have huniq : ∀ a M, F.IsDiffOf F (act.act a) M → R a = M :=
    fun a M h => (hdiff a).unique (hR a) h
  have hone : R 1 = 1 := huniq 1 1 (by
    intro u c h
    simpa [act.one] using h)
  have hmul : ∀ a b, R (a * b) = R a * R b := fun a b => by
    rw [mul_comm a b]
    refine huniq _ _ ?_
    intro u c h
    rw [act.mul, ← Category.assoc]
    exact hR a _ _ (hR b u c h)
  have hadd : ∀ a b, R (a + b) = R a + R b := fun a b => by
    refine huniq _ _ ?_
    intro u c h
    rw [act.add, comp_mul]
    exact _root_.GlobalTheory.CM.IntCoord.isCoord_mul F (hR a u c h) (hR b u c h)

  have hspan : Submodule.span K (F.lieLat :
      Set (Fin F.P₀.g → K)) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hφ0 (LinearMap.ext h)
    have hM : F.IsDiffOf F (act.act 1) (1 + φ.smulRight x) := by
      intro u c h
      have hφc : φ c = 0 := LinearMap.mem_ker.1 (hle (Submodule.subset_span ((hlie c).2 ⟨u, h⟩)))
      simpa [act.one, hφc] using h
    have h1 := LinearMap.congr_fun (hone.symm.trans (huniq 1 _ hM)) x
    simp at h1
    rcases h1 with h1 | h1
    · exact hx h1
    · exact hx (by simp [h1])
  have hlat : ∀ τ : O →+* 𝓞 K, ∀ c, c ∈ F.eigLat act τ ↔
      c ∈ F.lieLat ∧ ∀ a, R a c = τ a • c := by
    intro τ c
    rw [heig O act τ c, hlie c]
    constructor
    · rintro ⟨u, hu, hcomb⟩
      exact ⟨⟨u, hu⟩, fun a =>
        hcoord (hR a u c hu) (_root_.GlobalTheory.CM.IntCoord.isCoord_smul F hu (hcomb a))⟩
    · rintro ⟨⟨u, hu⟩, hc⟩
      refine ⟨u, hu, fun a => ?_⟩
      have hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb ![τ a] ![u] (_root_.GlobalTheory.CM.IntCoord.sc (τ a) ≫ u) :=
        (_root_.GlobalTheory.CM.IntCoord.isLieComb_one_iff _ _ _).2 rfl
      have he := hinj _ _ _ (hR a u c hu)
        (by rw [hc a]; exact _root_.GlobalTheory.CM.IntCoord.isCoord_smul F hu hs)
      rw [he]
      exact hs
  refine ⟨RingHom.mk' ⟨⟨R, hone⟩, hmul⟩ hadd, fun a => hR a, fun τ c => ⟨hlat τ c, ?_⟩⟩
  show _ ↔ ∀ a, R a c = τ a • c
  constructor
  · intro hc
    refine Submodule.span_induction (p := fun c _ => ∀ a, R a c = τ a • c) ?_ ?_ ?_ ?_ hc
    · exact fun x hx a => ((hlat τ x).1 hx).2 a
    · intro a
      simp
    · intro x y _ _ hx hy a
      rw [map_add, hx, hy, smul_add]
    · intro k x _ hx a
      rw [map_smul, hx, smul_comm]
  · intro hc
    have hcspan : c ∈ Submodule.span K (F.lieLat :
        Set (Fin F.P₀.g → K)) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, rfl⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 K))).1 hcspan
    rw [Submodule.span_eq] at hy
    have hzy : (z : 𝓞 K) • (IsLocalization.mk' K (1 : 𝓞 K) z • y) = y := by
      rw [← smul_assoc, Algebra.smul_def (z : 𝓞 K) (IsLocalization.mk' K (1 : 𝓞 K) z),
        IsLocalization.mk'_spec', map_one, one_smul]
    have hyeig : ∀ a, R a y = τ a • y := fun a => by
      rw [← hzy, LinearMap.map_smul_of_tower, hc a, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((hlat τ y).2 ⟨hy, hyeig⟩))

end GlobalTheory.CM.GenFib
