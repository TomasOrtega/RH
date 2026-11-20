import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNsmulMemOfSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelDenom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Unfold `Formalism.L2.Herm.hatL Formalism.UG.latS at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨l, hl, rfl⟩` from `hy`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨c • l, hc l hl, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[nsmul_eq_mul, map_mul, map_natCast]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [smul_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul a y _ hy`. Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ a hy`.
-/
theorem natCast_smul_mem_hatL_std (Λ : Submodule (𝓞 E) (Fin n → E)) (c : ℕ)
    (hc : ∀ y ∈ Λ, c • y ∈ Formalism.L2.Col.stdLat E n) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hx : x ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    (c : E ⊗[F] Formalism.L2.Herm.Af F) • x ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.L2.Col.stdLat E n) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨c • l, hc l hl, ?_⟩
    funext i
    simp [nsmul_eq_mul, map_mul, map_natCast]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hy

/- English proof (translation)
Take `⟨S, hS⟩` from `hfg`. Take `⟨c, hc, h⟩` from `GlobalTheory.LatSandwich.exists_nsmul_le S (Formalism.L2.Pj.stdLat E n) (fun x _ => GlobalTheory.LatSandwich.exists_nsmul_mem_stdLat x)`. Conclude with `⟨c, hc, fun y hy => h y (by rw [hS]; exact hy)⟩`.
-/
theorem exists_nsmul_le_std (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG) :
    ∃ c : ℕ, 0 < c ∧ ∀ y ∈ Λ, c • y ∈ Formalism.L2.Col.stdLat E n := by
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨c, hc, h⟩ := GlobalTheory.LatSandwich.exists_nsmul_le S (Formalism.L2.Pj.stdLat E n)
    (fun x _ => GlobalTheory.LatSandwich.exists_nsmul_mem_stdLat x)
  exact ⟨c, hc, fun y hy => h y (by rw [hS]; exact hy)⟩

/- English proof (translation)
Take `⟨c, hc, h⟩` from `GlobalTheory.LatSandwich.exists_nsmul_le (Finset.univ.image fun j : Fin n => (Pi.single j (1 : E) : Fin n → E)) Λ (fun x _ => GlobalTheory.LatSandwich.exists_nsmul_mem_of_span Λ hsp x)`. Conclude with `⟨c, hc, fun j => h _ (Submodule.subset_span (by simp))⟩`.
-/
theorem exists_nsmul_single_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∀ j, c • (Pi.single j (1 : E) : Fin n → E) ∈ Λ := by
  classical
  obtain ⟨c, hc, h⟩ := GlobalTheory.LatSandwich.exists_nsmul_le (Finset.univ.image fun j : Fin n => (Pi.single j (1 : E) : Fin n → E)) Λ
    (fun x _ => GlobalTheory.LatSandwich.exists_nsmul_mem_of_span Λ hsp x)
  exact ⟨c, hc, fun j => h _ (Submodule.subset_span (by simp))⟩

end GlobalTheory.LevelDenom

namespace GlobalTheory.LevelDenom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Take `⟨a, ha, hae⟩` from `exists_nsmul_single_mem Λ hsp`. Take `⟨c, hc0, hce⟩` from `exists_nsmul_le_std Λ hfg`. Use `⟨a * c, Nat.mul_pos ha hc0, fun k hk i j => ?_⟩` and prove the remaining obligations. Establish `hs` using `hk.2.1`. Establish `hzmem : (fun l => Formalism.UG.inclE (Formalism.L2.Herm.Af F) ((a • (Pi.single j (1 : E) : Fin n → E)) l)) ∈ Formalism.L2.Herm.hatL (F` using `F) Λ := Submodule.subset_span ⟨_, hae j, rfl⟩`.

Establish `ez : (fun l => Formalism.UG.inclE (Formalism.L2.Herm.Af F) ((a • (Pi.single j (1 : E) : Fin n → E)) l)) = (a : E ⊗[F] Formalism.L2.Herm.Af F) • (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)`. Use function extensionality and compare the values at `l`. Distinguish the cases in `e : l = j`. Substitute `e` using the available equality. Simplify using `[nsmul_eq_mul]`.

Simplify using `[Pi.single_eq_of_ne e, nsmul_eq_mul]`. Rewrite `hzmem` using `[ez]`. Establish `hkz` using `(hs _).1 hzmem`. Establish `h2` using `natCast_smul_mem_hatL_std Λ c hce _ hkz`. Rewrite `h2` using `[Formalism.L2.Col.mem_latS_std]`.

Establish `h3` using `h2 i`. Rewrite `h3` using `[Matrix.mulVec_smul]`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Simplify using `[Matrix.mulVec_single_one, mul_comm, mul_left_comm, mul_assoc]`.
-/
theorem exists_denom_stab (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ b : ℕ, 0 < b ∧ ∀ k ∈ congLev hc J Λ ⊤, ∀ i j,
      (b : E ⊗[F] Formalism.L2.Herm.Af F) * k.1 i j ∈ Formalism.L2.Herm.intAf F E := by
  classical
  obtain ⟨a, ha, hae⟩ := exists_nsmul_single_mem Λ hsp
  obtain ⟨c, hc0, hce⟩ := exists_nsmul_le_std Λ hfg
  refine ⟨a * c, Nat.mul_pos ha hc0, fun k hk i j => ?_⟩
  have hs := hk.2.1
  have hzmem : (fun l => Formalism.UG.inclE (Formalism.L2.Herm.Af F) ((a • (Pi.single j (1 : E) : Fin n → E)) l)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ := Submodule.subset_span ⟨_, hae j, rfl⟩
  have ez : (fun l => Formalism.UG.inclE (Formalism.L2.Herm.Af F) ((a • (Pi.single j (1 : E) : Fin n → E)) l)) =
      (a : E ⊗[F] Formalism.L2.Herm.Af F) • (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := by
    funext l
    by_cases e : l = j
    · subst e; simp [nsmul_eq_mul]
    · simp [Pi.single_eq_of_ne e, nsmul_eq_mul]
  rw [ez] at hzmem
  have hkz := (hs _).1 hzmem
  have h2 := natCast_smul_mem_hatL_std Λ c hce _ hkz
  rw [Formalism.L2.Col.mem_latS_std] at h2
  have h3 := h2 i
  rw [Matrix.mulVec_smul] at h3
  convert h3 using 1
  simp [Matrix.mulVec_single_one, mul_comm, mul_left_comm, mul_assoc]

end GlobalTheory.LevelDenom

namespace GlobalTheory.LevelDenom

/- English proof (translation)
Introduce `D V Λ hΛ`. Use `haveI := hΛ.1`. Conclude with `exists_denom_stab D.sp.cm V.gram Λ (Submodule.IsLattice.fg (A := D.host.E)) (Submodule.IsLattice.span_eq_top (A := D.host.E))`.
-/
theorem exists_denom_congLev : ∀ (D : D7) (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∃ b : ℕ, 0 < b ∧ ∀ k ∈ congLev D.sp.cm V.gram Λ ⊤, ∀ i j, (b : Lev.EAf D) * k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D V Λ hΛ
  haveI := hΛ.1
  exact exists_denom_stab D.sp.cm V.gram Λ (Submodule.IsLattice.fg (A := D.host.E))
    (Submodule.IsLattice.span_eq_top (A := D.host.E))

end GlobalTheory.LevelDenom
