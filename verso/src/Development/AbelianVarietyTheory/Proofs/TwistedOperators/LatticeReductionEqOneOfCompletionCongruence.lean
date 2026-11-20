import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevRedTriv

open Formalism.L2.DIV

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Use `set B : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 with hB`. Use `revert i`. Use `Submodule.span_induction (p := fun z _ => ∀ i, ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (B *ᵥ z) i) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `Submodule.smul_induction_on (p := fun x => ∀ i, ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (B *ᵥ fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) i) hx ?_ ?_` and prove the remaining obligations.

Introduce `p hp l hl i`. Establish `hlm : (fun i => Formalism.UG.inclE (F` using `F) (Formalism.L2.Herm.Af F) (l i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := Submodule.subset_span ⟨l, hl, rfl⟩`. Establish `ht` using `(hβ _).1 hlm i`. Use `⟨oToS F E p * ⟨_, ht⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp), ?_⟩` and prove the remaining obligations. Establish `e : (fun i => Formalism.UG.inclE (F` using `F) (Formalism.L2.Herm.Af F) ((p • l) i)) = ((oToS F E p : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) • (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) := by`.

Use function extensionality and compare the values at `k`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, oToS_coe, smul_eq_mul]`. Use `show ((p : E) * l k) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = (algebraMap (𝓞 E) E p) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) * ((l k) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F))`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Subring.coe_mul]`.

Introduce `x₁ x₂ h₁ h₂ i`. Take `⟨s₁, hs₁, e₁⟩` from `h₁ i`. Take `⟨s₂, hs₂, e₂⟩` from `h₂ i`. Use `⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, ?_⟩` and prove the remaining obligations. Establish `e : (fun i => Formalism.UG.inclE (F` using `F) (Formalism.L2.Herm.Af F) ((x₁ + x₂) i)) = (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x₁ i)) + (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x₂ i)) := by`.

Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Rewrite using `[e, Matrix.mulVec_add, Pi.add_apply, Subring.coe_add, e₁, e₂]`. Introduce `i`. Conclude with `⟨0, Ideal.zero_mem _, by simp⟩`.

Introduce `a c _ _ ha hc i`. Take `⟨s₁, hs₁, e₁⟩` from `ha i`. Take `⟨s₂, hs₂, e₂⟩` from `hc i`. Conclude with `⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, by rw [Matrix.mulVec_add, Pi.add_apply, Subring.coe_add, e₁, e₂]⟩`. Introduce `c a _ ha i`.

Take `⟨s, hs, e⟩` from `ha i`. Use `⟨c * s, Ideal.mul_mem_left _ _ hs, ?_⟩` and prove the remaining obligations. Establish `: c • a = ((c : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) • a` using `rfl`. Rewrite using `[this, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Subring.coe_mul, e]`.
-/
theorem coord_mem_idS {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (PP : Pl E) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (PP.asIdeal • Λ)) (i : Fin n) :
    ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
      (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ z) i := by
  set B : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 with hB
  revert i
  refine Submodule.span_induction
    (p := fun z _ => ∀ i, ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (B *ᵥ z) i)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.smul_induction_on
      (p := fun x => ∀ i, ∃ s ∈ idS F PP.asIdeal, ((s : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
        (B *ᵥ fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) i) hx ?_ ?_
    · intro p hp l hl i
      have hlm : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        Submodule.subset_span ⟨l, hl, rfl⟩
      have ht := (hβ _).1 hlm i
      refine ⟨oToS F E p * ⟨_, ht⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp), ?_⟩
      have e : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((p • l) i)) =
          ((oToS F E p : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) •
            (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) := by
        funext k
        rw [Pi.smul_apply, Pi.smul_apply, oToS_coe, smul_eq_mul]
        show ((p : E) * l k) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) =
          (algebraMap (𝓞 E) E p) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) * ((l k) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F))
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Subring.coe_mul]
    · intro x₁ x₂ h₁ h₂ i
      obtain ⟨s₁, hs₁, e₁⟩ := h₁ i
      obtain ⟨s₂, hs₂, e₂⟩ := h₂ i
      refine ⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, ?_⟩
      have e : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((x₁ + x₂) i)) =
          (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x₁ i)) +
            (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x₂ i)) := by
        funext k; simp
      rw [e, Matrix.mulVec_add, Pi.add_apply, Subring.coe_add, e₁, e₂]
  · intro i
    exact ⟨0, Ideal.zero_mem _, by simp⟩
  · intro a c _ _ ha hc i
    obtain ⟨s₁, hs₁, e₁⟩ := ha i
    obtain ⟨s₂, hs₂, e₂⟩ := hc i
    exact ⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, by rw [Matrix.mulVec_add, Pi.add_apply, Subring.coe_add, e₁, e₂]⟩
  · intro c a _ ha i
    obtain ⟨s, hs, e⟩ := ha i
    refine ⟨c * s, Ideal.mul_mem_left _ _ hs, ?_⟩
    have : c • a = ((c : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) • a := rfl
    rw [this, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Subring.coe_mul, e]

/- English proof (translation)
Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem coe_sub_one_apply (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (i j : Fin n) :
    (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = ((intGL F E n y).1 - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.
-/
theorem conj_sub_one {R : Type} [CommRing R] {m : ℕ} (β : GL (Fin m) R) (X Y : Matrix (Fin m) (Fin m) R)
    (h : X = β.1 * Y * (β⁻¹).1) : Y - 1 = (β⁻¹).1 * (X - 1) * β.1 := by
  subst h
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hc, Pi.sub_apply, map_sub, RingHom.map_mulVec, hu, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← hu]`. Both sides reduce to the same expression.
-/
theorem map_smul_sub {A B : Type} [CommRing A] [CommRing B] {m : ℕ} (f : A →+* B) (c : A) (c' : B) (hc : f c = c')
    (M : Matrix (Fin m) (Fin m) A) (u : Fin m → A) (w : Fin m → B) (hu : ⇑f ∘ u = w) :
    (fun i => f ((c • (M *ᵥ u - u)) i)) = c' • ((M.map f - 1) *ᵥ w) := by
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hc, Pi.sub_apply, map_sub,
    RingHom.map_mulVec, hu, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← hu]
  rfl

/- English proof (translation)
Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← e2, Matrix.mulVec_single_one]`. Both sides reduce to the same expression.
-/
theorem col_entry {R : Type} [CommRing R] {m : ℕ} (β : GL (Fin m) R) (X Y : Matrix (Fin m) (Fin m) R)
    (e2 : Y - 1 = (β⁻¹).1 * (X - 1) * β.1) (c : R) (i j : Fin m) :
    ((β⁻¹).1 *ᵥ (c • ((X - 1) *ᵥ (β.1 *ᵥ Pi.single j 1)))) i = c * (Y - 1) i j := by
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← e2,
    Matrix.mulVec_single_one]
  rfl

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Establish `e2 : (intGL F E n y).1 - 1 = (β⁻¹).1 * ((frGL β y).1 - 1) * β.1` using `conj_sub_one β _ _ rfl`. Establish `hprime : PP.asIdeal.IsPrime` using `PP.isPrime`. Establish `hb0 : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hb`. Rewrite using `[redFn_frGL]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Take `⟨s, hs, es⟩` from `coord_mem_idS hβ PP (h j) i`.

Apply the tactic sequence `rw [col_entry β _ _ e2] at es`. Establish `es' : s = oToS F E b * (y.1 - 1) i j`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subring.coe_mul, coe_sub_one_apply, es]`. Establish `e6 : resS F PP ((y.1 - 1) i j) = 0`.

Establish `h0 : resS F PP s = 0`. Rewrite using `[GlobalTheory.GeoActCompare.resS_eq_resI, GlobalTheory.GeoActCompare.resI_eq_zero_iff]`. Conclude with `hs`. Rewrite `h0` using `[es', map_mul, resS_oToS]`. Conclude with `(mul_eq_zero.1 h0).resolve_left hb0`.

Use `show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j`. Rewrite `e6` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[e6, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem redFn_eq_one_of_cols {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (PP : Pl E) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ St β) (b : 𝓞 E)
    (hb : b ∉ PP.asIdeal)
    (h : ∀ j, ((oToS F E b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) •
      ((x.1 - 1) *ᵥ (β.1 *ᵥ Pi.single j 1)) ∈ Formalism.L2.Herm.hatL (F := F) (PP.asIdeal • Λ)) :
    redFn β PP x = 1 := by
  obtain ⟨y, rfl⟩ := hx
  have e2 : (intGL F E n y).1 - 1 = (β⁻¹).1 * ((frGL β y).1 - 1) * β.1 := conj_sub_one β _ _ rfl
  have hprime : PP.asIdeal.IsPrime := PP.isPrime
  have hb0 : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hb
  rw [redFn_frGL]
  apply Units.ext
  ext i j
  obtain ⟨s, hs, es⟩ := coord_mem_idS hβ PP (h j) i
  rw [col_entry β _ _ e2] at es
  have es' : s = oToS F E b * (y.1 - 1) i j := by
    apply Subtype.ext
    rw [Subring.coe_mul, coe_sub_one_apply, es]
  have e6 : resS F PP ((y.1 - 1) i j) = 0 := by
    have h0 : resS F PP s = 0 := by
      rw [GlobalTheory.GeoActCompare.resS_eq_resI, GlobalTheory.GeoActCompare.resI_eq_zero_iff]; exact hs
    rw [es', map_mul, resS_oToS] at h0
    exact (mul_eq_zero.1 h0).resolve_left hb0
  show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at e6
  rw [e6, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end General

section Adelic

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `eX : (Lev.finE V k).1 = (fmt V k).map (GlobalTheory.LevSplit.swp D.host.F D.host.E)` using `rfl`. Rewrite using `[eX]`. Use `choose u hu using fun i => (GlobalTheory.LevSplit.swp_bij (F := D.host.F) (E := D.host.E)).2 (w i)`. Establish `hu' : (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (u i)) = w` using `funext hu`. Establish `hc : ⇑(GlobalTheory.LevSplit.swp D.host.F D.host.E) ∘ u = w` using `funext hu`.

Establish `hum : u ∈ hatV L` using `(GlobalTheory.LevSplit.latHat_iff L u).2 (by rw [hu']; exact hw)`. Establish `h1` using `(GlobalTheory.LevSplit.latHat_iff (PP.asIdeal • L) _).1 (h u hum)`. Establish `eb : GlobalTheory.LevSplit.swp D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) = ((oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)`. Rewrite using `[GlobalTheory.LevSplit.swp_tmul, oToS_coe]`. Rewrite `h1` using `[map_smul_sub (GlobalTheory.LevSplit.swp D.host.F D.host.E) _ _ eb (fmt V k) u w hc]`.

Conclude with `h1`.
-/
theorem col_cong (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D))
    (hβ : Formalism.L2.DIV.IsFrame β L) (k : GA D V) (PP : Formalism.L2.DIV.Pl D.host.E) (b : 𝓞 D.host.E)
    (h : ∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (fmt V k *ᵥ u - u) ∈ hatV (PP.asIdeal • L))
    (w : Fin V.rank → Lev.EAf D) (hw : w ∈ Formalism.L2.Herm.hatL (F := D.host.F) L) :
    ((oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) •
      (((Lev.finE V k).1 - 1) *ᵥ w) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (PP.asIdeal • L) := by
  have eX : (Lev.finE V k).1 = (fmt V k).map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := rfl
  rw [eX]
  choose u hu using fun i => (GlobalTheory.LevSplit.swp_bij (F := D.host.F) (E := D.host.E)).2 (w i)
  have hu' : (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (u i)) = w := funext hu
  have hc : ⇑(GlobalTheory.LevSplit.swp D.host.F D.host.E) ∘ u = w := funext hu
  have hum : u ∈ hatV L := (GlobalTheory.LevSplit.latHat_iff L u).2 (by rw [hu']; exact hw)
  have h1 := (GlobalTheory.LevSplit.latHat_iff (PP.asIdeal • L) _).1 (h u hum)
  have eb : GlobalTheory.LevSplit.swp D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) =
      ((oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) := by
    rw [GlobalTheory.LevSplit.swp_tmul, oToS_coe]
  rw [map_smul_sub (GlobalTheory.LevSplit.swp D.host.F D.host.E) _ _ eb (fmt V k) u w hc] at h1
  exact h1

/- English proof (translation)
The claim follows from `redFn_eq_one_of_cols hβ PP _ hk b hb fun j => col_cong D V L β hβ k PP b h _ (GlobalTheory.ChainOnto.LStab.col_mem_hatL hβ j)`.
-/
theorem redFn_eq_one_of_cong (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D))
    (hβ : Formalism.L2.DIV.IsFrame β L) (k : GA D V) (hk : Lev.finE V k ∈ Formalism.L2.DIV.St β)
    (PP : Formalism.L2.DIV.Pl D.host.E) (b : 𝓞 D.host.E) (hb : b ∉ PP.asIdeal)
    (h : ∀ u ∈ hatV L, ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (fmt V k *ᵥ u - u) ∈ hatV (PP.asIdeal • L)) :
    Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 :=
  redFn_eq_one_of_cols hβ PP _ hk b hb fun j =>
    col_cong D V L β hβ k PP b h _ (GlobalTheory.ChainOnto.LStab.col_mem_hatL hβ j)

end Adelic

end GlobalTheory.LevRedTriv
