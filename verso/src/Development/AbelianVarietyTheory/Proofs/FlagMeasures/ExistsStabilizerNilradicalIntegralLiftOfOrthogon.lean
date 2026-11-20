import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.NilLift

/- English proof (translation)
Establish `hu : ∀ x : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O V) x)` using `fun s => by`. Use `isLocalizedModule_id (nonZeroDivisors O) V K` as an intermediate fact. Conclude with `IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s`. Establish `hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype` using `{ map_units := hu surj := fun y => by`. Establish `hy : y ∈ Submodule.span K (Λ : Set V)` using `by rw [hspan]; trivial`.

Take `⟨s, hs⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy`. Rewrite `hs` using `[Submodule.span_eq]`. Conclude with `⟨(⟨_, hs⟩, s), rfl⟩`. Use `exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }`. Establish `: Module.Finite O Λ` using `Module.Finite.iff_fg.2 hfg`.

Set `Q : Submodule O Λ` to `P.comap Λ.subtype`. Establish `: Module.Flat O (Λ ⧸ Q)`. Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`. Introduce `q hq`. Take `⟨v, rfl⟩` from `Q.mkQ_surjective q`.

Take `⟨c, hc⟩` from `hq`. Establish `h1 : Q.mkQ ((c : O) • v) = 0` using `by rw [map_smul]; exact hc`. Rewrite `h1` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hsat c (nonZeroDivisors.coe_ne_zero c) v v.2 h1`.

Establish `: Module.FinitePresentation O (Λ ⧸ Q)` using `Module.finitePresentation_of_finite _ _`. Establish `: Module.Projective O (Λ ⧸ Q)` using `Module.Flat.projective_of_finitePresentation`. Take `⟨s, hs⟩` from `Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective`. Set `π : Λ →ₗ[O] Λ` to `LinearMap.id - s ∘ₗ Q.mkQ`. Establish `hπ : ∀ v, π v ∈ Q`.

Introduce `v`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]`. Establish `h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v` using `LinearMap.congr_fun hs _`. Simplify using `only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]`. Establish `hπ' : ∀ v ∈ Q, π v = v`.

Introduce `v hv`. Establish `h1 : Q.mkQ v = 0` using `by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Simplify using `only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]`. Set `g : V →ₗ[K] V` to `LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype (Λ.subtype ∘ₗ π) hu)`. Establish `hg : ∀ y : Λ, g y = π y` using `fun y => IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hu y`.

Use `⟨g, fun z hz => ?_, fun z hz hP => ?_⟩` and prove the remaining obligations. Rewrite using `[hg ⟨z, hz⟩]`. Conclude with `hπ _`. Rewrite using `[hg ⟨z, hz⟩, hπ' ⟨z, hz⟩ hP]`.
-/
theorem exists_projector {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ P : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤)
    (hsat : ∀ c : O, c ≠ 0 → ∀ v ∈ Λ, c • v ∈ P → v ∈ P) :
    ∃ g : V →ₗ[K] V, (∀ z ∈ Λ, g z ∈ P) ∧ ∀ z ∈ Λ, z ∈ P → g z = z := by
  have hu : ∀ x : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O V) x) := fun s => by
    have := isLocalizedModule_id (nonZeroDivisors O) V K
    exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := hu
      surj := fun y => by
        have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
        obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
        rw [Submodule.span_eq] at hs
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := P.comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c (nonZeroDivisors.coe_ne_zero c) v v.2 h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  let g : V →ₗ[K] V := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype (Λ.subtype ∘ₗ π) hu)
  have hg : ∀ y : Λ, g y = π y := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hu y
  refine ⟨g, fun z hz => ?_, fun z hz hP => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact hπ _
  · rw [hg ⟨z, hz⟩, hπ' ⟨z, hz⟩ hP]

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

local notation "𝒽" => Formalism.UG.hform (starRingEnd E) J

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply, starRingEnd_apply]`.
-/
theorem form_eq (x y : Fin n → E) : 𝒽 x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply,
    starRingEnd_apply]

/- English proof (translation)
Establish `h : ∀ i j, star (J i j) = J j i` using `fun i j => congrFun (congrFun hJ j) i`. Simplify using `only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, h]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem form_star (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (x y : Fin n → E) :
    star (𝒽 x y) = 𝒽 y x := by
  have h : ∀ i j, star (J i j) = J j i := fun i j => congrFun (congrFun hJ j) i
  simp only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Rewrite using `[form_eq, form_eq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), Matrix.one_mul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]`.
-/
theorem form_adj (hJ : J.det ≠ 0) (Ψ : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    𝒽 x ((J⁻¹ * Ψᴴ * J) *ᵥ y) = 𝒽 (Ψ *ᵥ x) y := by
  rw [form_eq, form_eq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), Matrix.one_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.star_mulVec]

/- English proof (translation)
Establish `h1 : J *ᵥ y = 0`. Use function extensionality and compare the values at `i`. Use `h (Pi.single i 1)` as an intermediate fact. Rewrite `this` using `[form_eq]`. Simplify `this` using `[Pi.star_single]`.

Conclude with `Matrix.eq_zero_of_mulVec_eq_zero hJ h1`.
-/
theorem eq_zero_of_form (hJ : J.det ≠ 0) (y : Fin n → E) (h : ∀ x, 𝒽 x y = 0) : y = 0 := by
  have h1 : J *ᵥ y = 0 := by
    funext i
    have := h (Pi.single i 1)
    rw [form_eq] at this
    simpa [Pi.star_single] using this
  exact Matrix.eq_zero_of_mulVec_eq_zero hJ h1

/- English proof (translation)
Simplify using `only [form_eq] at h ⊢`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem s hs => exact h s hs`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]`.

Consider the case `smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]`.
-/
theorem form_span_left (S : Set (Fin n → E)) (y : Fin n → E) (h : ∀ s ∈ S, 𝒽 s y = 0)
    (w : Fin n → E) (hw : w ∈ Submodule.span E S) : 𝒽 w y = 0 := by
  simp only [form_eq] at h ⊢
  induction hw using Submodule.span_induction with
  | mem s hs => exact h s hs
  | zero => simp
  | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
  | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]

/- English proof (translation)
Establish `hA : ∀ u ∈ perpSet (starRingEnd E) J W, (J⁻¹ * Ψᴴ * J) *ᵥ u = 0` using `fun u hu => eq_zero_of_form J hdet _ fun v => by rw [form_adj J hdet]; exact hu _ (h1 v)`. Establish `hsr : ∀ a b c : Fin n → E, 𝒽 a (b - c) = 𝒽 a b - 𝒽 a c` using `fun a b c => by`. Simplify using `only [form_eq, Matrix.mulVec_sub, dotProduct_sub]`. Establish `hsl : ∀ a b c : Fin n → E, 𝒽 (b - c) a = 𝒽 b a - 𝒽 c a` using `fun a b c => by`. Simplify using `only [form_eq, star_sub, sub_dotProduct]`.

Use `⟨⟨fun u u' => ?_, fun u w hw => ?_, fun u hu => ?_, fun u hu => ?_⟩, hA⟩` and prove the remaining obligations. Rewrite using `[Matrix.sub_mulVec, Matrix.sub_mulVec, hsr, hsl, form_adj J hdet, ← form_star J hJ u' ((J⁻¹ * Ψᴴ * J) *ᵥ u), form_adj J hdet, form_star J hJ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Matrix.sub_mulVec, hsr, form_adj J hdet, h2 w hw, hW _ (h1 u) w hw, form_eq]`. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.sub_mulVec, hA u hu, sub_zero]`. Conclude with `h1 u`. Rewrite using `[Matrix.sub_mulVec, hA u (hW u hu), sub_zero]`. Conclude with `h2 u hu`.
-/
theorem inNil_sub_adj (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (hdet : J.det ≠ 0)
    (W : Submodule E (Fin n → E)) (hW : ∀ w ∈ W, w ∈ perpSet (starRingEnd E) J W)
    (Ψ : Matrix (Fin n) (Fin n) E) (h1 : ∀ u, Ψ *ᵥ u ∈ W) (h2 : ∀ u ∈ W, Ψ *ᵥ u = 0) :
    InNil (starRingEnd E) J W (Ψ - J⁻¹ * Ψᴴ * J) ∧
      ∀ u ∈ perpSet (starRingEnd E) J W, (J⁻¹ * Ψᴴ * J) *ᵥ u = 0 := by
  have hA : ∀ u ∈ perpSet (starRingEnd E) J W, (J⁻¹ * Ψᴴ * J) *ᵥ u = 0 := fun u hu =>
    eq_zero_of_form J hdet _ fun v => by rw [form_adj J hdet]; exact hu _ (h1 v)
  have hsr : ∀ a b c : Fin n → E, 𝒽 a (b - c) = 𝒽 a b - 𝒽 a c := fun a b c => by
    simp only [form_eq, Matrix.mulVec_sub, dotProduct_sub]
  have hsl : ∀ a b c : Fin n → E, 𝒽 (b - c) a = 𝒽 b a - 𝒽 c a := fun a b c => by
    simp only [form_eq, star_sub, sub_dotProduct]
  refine ⟨⟨fun u u' => ?_, fun u w hw => ?_, fun u hu => ?_, fun u hu => ?_⟩, hA⟩
  · rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hsr, hsl, form_adj J hdet,
      ← form_star J hJ u' ((J⁻¹ * Ψᴴ * J) *ᵥ u), form_adj J hdet, form_star J hJ]
    ring
  · rw [Matrix.sub_mulVec, hsr, form_adj J hdet, h2 w hw, hW _ (h1 u) w hw, form_eq]
    simp
  · rw [Matrix.sub_mulVec, hA u hu, sub_zero]
    exact h1 u
  · rw [Matrix.sub_mulVec, hA u (hW u hu), sub_zero]
    exact h2 u hu

end Form

/- English proof (translation)
Use `⟨fun h => ?_, fun h => Submodule.subset_span h⟩` and prove the remaining obligations. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem y hy => exact hy`. Consider the case `zero => exact ⟨zero_mem _, fun s _ => by simp [form_eq]⟩`. Consider the case `add y z _ _ hy hz`.

Conclude with `⟨add_mem hy.1 hz.1, fun s hs => by`. Rewrite using `[form_eq, Matrix.mulVec_add, dotProduct_add, ← form_eq, ← form_eq, hy.2 s hs, hz.2 s hs, add_zero]⟩`. Consider the case `smul c y _ hy`. Conclude with `⟨Submodule.smul_mem _ _ hy.1, fun s hs => by`. Rewrite using `[form_eq, Matrix.mulVec_smul, dotProduct_smul, ← form_eq, hy.2 s hs, smul_zero]⟩`.
-/
theorem mem_perpIn_iff (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) (y : Fin I.n → I.E) :
    y ∈ perpIn I x S ↔ y ∈ lamX I x ∧ ∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨zero_mem _, fun s _ => by simp [form_eq]⟩
  | add y z _ _ hy hz =>
    exact ⟨add_mem hy.1 hz.1, fun s hs => by
      rw [form_eq, Matrix.mulVec_add, dotProduct_add, ← form_eq, ← form_eq, hy.2 s hs, hz.2 s hs, add_zero]⟩
  | smul c y _ hy =>
    exact ⟨Submodule.smul_mem _ _ hy.1, fun s hs => by
      rw [form_eq, Matrix.mulVec_smul, dotProduct_smul, ← form_eq, hy.2 s hs, smul_zero]⟩

/- English proof (translation)
Introduce `I x R hR Φ hΦ0 hΦ`. Take `⟨-, hfg, hspan, hdual, -⟩` from `GlobalTheory.PointLattice.lamX_selfDual I x`. Take `⟨g, hg, hg'⟩` from `exists_projector (lamX I x) (perpIn I x R) hfg hspan (fun c hc v hv h => by`. Use `(mem_perpIn_iff I x R v).2 ⟨hv, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h1` using `((mem_perpIn_iff I x R _).1 h).2 s hs`.

Rewrite `h1` using `[form_eq, Matrix.mulVec_smul, dotProduct_smul, ← form_eq]`. Conclude with `(smul_eq_zero.1 h1).resolve_left hc)`. Use `set W := Submodule.span I.E (R : Set (Fin I.n → I.E)) with hWdef`. Set `Ψ : Matrix (Fin I.n) (Fin I.n) I.E` to `Φ * LinearMap.toMatrix' g`. Establish `hΨ : ∀ u, Ψ *ᵥ u = Φ *ᵥ g u` using `fun u => by`.

Rewrite using `[← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]`. Establish `hPΛ : ∀ y ∈ perpIn I x R, y ∈ lamX I x` using `fun y hy => ((mem_perpIn_iff I x R y).1 hy).1`. Establish `hΨP : ∀ y ∈ perpIn I x R, Ψ *ᵥ y = Φ *ᵥ y` using `fun y hy => by rw [hΨ, hg' y (hPΛ y hy) hy]`. Establish `hΨΛ : ∀ y ∈ lamX I x, Ψ *ᵥ y ∈ R` using `fun y hy => by rw [hΨ]; exact hΦ _ (hg y hy)`. Establish `hP : ∀ y ∈ perpIn I x R, y ∈ perpSet (starRingEnd I.E) I.J W` using `fun y hy => form_span_left I.J _ y ((mem_perpIn_iff I x R y).1 hy).2`.

Establish `hW : ∀ w ∈ W, w ∈ perpSet (starRingEnd I.E) I.J W` using `fun w hw w' hw' => by`. Rewrite using `[← form_star I.J I.J_herm, form_span_left I.J _ w' (fun s hs => ?_) w hw, star_zero]`. Rewrite using `[← form_star I.J I.J_herm, hP s (hR hs) w' hw', star_zero]`. Establish `h1 : ∀ u, Ψ *ᵥ u ∈ W` using `fun u => by`. Establish `: Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) ≤ W.comap (Matrix.mulVecLin Ψ)` using `Submodule.span_le.2 fun y hy => Submodule.subset_span (hΨΛ y hy)`.

Conclude with `this (hspan ▸ Submodule.mem_top)`. Establish `h2 : ∀ u ∈ W, Ψ *ᵥ u = 0` using `fun u hu => by`. Establish `: W ≤ LinearMap.ker (Matrix.mulVecLin Ψ)` using `Submodule.span_le.2 fun y hy => (hΨP y (hR hy)).trans (hΦ0 y hy)`. Conclude with `this hu`. Take `⟨hN, hA⟩` from `inNil_sub_adj I.J I.J_herm I.J_det W hW Ψ h1 h2`.

Use `⟨_, ⟨hN, fun u hu => ?_⟩, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.sub_mulVec]`. Use `sub_mem (hPΛ _ (hR (hΨΛ u hu))) ((hdual _).2 fun z hz => ?_)` and prove the remaining obligations. Rewrite using `[form_adj I.J I.J_det]`. Conclude with `(hdual u).1 hu _ (hPΛ _ (hR (hΨΛ z hz)))`.

Rewrite using `[Matrix.sub_mulVec, hA y (hP y hy), sub_zero, hΨP y hy]`.
-/
theorem exists_nilInt_lift : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), R ≤ perpIn I x R → ∀ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ R, Φ *ᵥ y = 0) → (∀ y ∈ perpIn I x R, Φ *ᵥ y ∈ R) → ∃ Y ∈ nilInt I x R, ∀ y ∈ perpIn I x R, Y *ᵥ y = Φ *ᵥ y := by
  intro I x R hR Φ hΦ0 hΦ
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨g, hg, hg'⟩ := exists_projector (lamX I x) (perpIn I x R) hfg hspan (fun c hc v hv h => by
    refine (mem_perpIn_iff I x R v).2 ⟨hv, fun s hs => ?_⟩
    have h1 := ((mem_perpIn_iff I x R _).1 h).2 s hs
    rw [form_eq, Matrix.mulVec_smul, dotProduct_smul, ← form_eq] at h1
    exact (smul_eq_zero.1 h1).resolve_left hc)
  set W := Submodule.span I.E (R : Set (Fin I.n → I.E)) with hWdef
  let Ψ : Matrix (Fin I.n) (Fin I.n) I.E := Φ * LinearMap.toMatrix' g
  have hΨ : ∀ u, Ψ *ᵥ u = Φ *ᵥ g u := fun u => by
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  have hPΛ : ∀ y ∈ perpIn I x R, y ∈ lamX I x := fun y hy => ((mem_perpIn_iff I x R y).1 hy).1
  have hΨP : ∀ y ∈ perpIn I x R, Ψ *ᵥ y = Φ *ᵥ y := fun y hy => by rw [hΨ, hg' y (hPΛ y hy) hy]
  have hΨΛ : ∀ y ∈ lamX I x, Ψ *ᵥ y ∈ R := fun y hy => by rw [hΨ]; exact hΦ _ (hg y hy)
  have hP : ∀ y ∈ perpIn I x R, y ∈ perpSet (starRingEnd I.E) I.J W := fun y hy =>
    form_span_left I.J _ y ((mem_perpIn_iff I x R y).1 hy).2
  have hW : ∀ w ∈ W, w ∈ perpSet (starRingEnd I.E) I.J W := fun w hw w' hw' => by
    rw [← form_star I.J I.J_herm, form_span_left I.J _ w' (fun s hs => ?_) w hw, star_zero]
    rw [← form_star I.J I.J_herm, hP s (hR hs) w' hw', star_zero]
  have h1 : ∀ u, Ψ *ᵥ u ∈ W := fun u => by
    have : Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) ≤ W.comap (Matrix.mulVecLin Ψ) :=
      Submodule.span_le.2 fun y hy => Submodule.subset_span (hΨΛ y hy)
    exact this (hspan ▸ Submodule.mem_top)
  have h2 : ∀ u ∈ W, Ψ *ᵥ u = 0 := fun u hu => by
    have : W ≤ LinearMap.ker (Matrix.mulVecLin Ψ) :=
      Submodule.span_le.2 fun y hy => (hΨP y (hR hy)).trans (hΦ0 y hy)
    exact this hu
  obtain ⟨hN, hA⟩ := inNil_sub_adj I.J I.J_herm I.J_det W hW Ψ h1 h2
  refine ⟨_, ⟨hN, fun u hu => ?_⟩, fun y hy => ?_⟩
  · rw [Matrix.sub_mulVec]
    refine sub_mem (hPΛ _ (hR (hΨΛ u hu))) ((hdual _).2 fun z hz => ?_)
    rw [form_adj I.J I.J_det]
    exact (hdual u).1 hu _ (hPΛ _ (hR (hΨΛ z hz)))
  · rw [Matrix.sub_mulVec, hA y (hP y hy), sub_zero, hΨP y hy]

end GlobalTheory.NilLift
