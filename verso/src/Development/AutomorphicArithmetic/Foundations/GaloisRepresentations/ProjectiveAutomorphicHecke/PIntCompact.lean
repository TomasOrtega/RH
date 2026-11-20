import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import GroundTheory.GlobalFields.Adele.Compact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

/- English proof (translation)
Establish `hO` using `GroundTheory.Global.isCompact_integralFiniteAdeles ℚ`. Establish `hB' : IsCompact (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) : Set AfQᵐᵒᵖ)` using `MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hO`. Establish `e : (ZU : Set AfQˣ) = Units.embedProduct _ ⁻¹' ((GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) ×ˢ (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ)))`. Use extensionality with `s`. Simplify using `only [SetLike.mem_coe, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, MulOpposite.unop_op, GroundTheory.Global.mem_integralFiniteAdeles]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2` using `(ZU.inv_mem h)`. Conclude with `⟨fun v => (h v).le, fun v => (h2 v).le⟩`. Introduce and unpack `⟨h1, h2⟩ v`.

Establish `h3 : Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) = 1`. Rewrite using `[← map_mul]`. Use `show Valued.v (((s : AfQ) * (↑s⁻¹ : AfQ)) v) = 1`. Rewrite using `[Units.mul_inv]`. Conclude with `map_one _`.

Use `le_antisymm (h1 v) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e]`. Conclude with `Units.isClosedEmbedding_embedProduct.isCompact_preimage (hO.prod hB')`.
-/
private theorem isCompact_ZU : IsCompact (ZU : Set AfQˣ) := by
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles ℚ
  have hB' : IsCompact (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) : Set AfQᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hO
  have e : (ZU : Set AfQˣ) = Units.embedProduct _ ⁻¹'
      ((GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) ×ˢ
        (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ))) := by
    ext s
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, MulOpposite.unop_op,
      GroundTheory.Global.mem_integralFiniteAdeles]
    constructor
    · intro h
      have h2 := (ZU.inv_mem h)
      exact ⟨fun v => (h v).le, fun v => (h2 v).le⟩
    · rintro ⟨h1, h2⟩ v
      have h3 : Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) = 1 := by
        rw [← map_mul]
        show Valued.v (((s : AfQ) * (↑s⁻¹ : AfQ)) v) = 1
        rw [Units.mul_inv]; exact map_one _
      refine le_antisymm (h1 v) ?_
      calc (1 : _) = Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) := h3.symm
        _ ≤ Valued.v ((s : AfQ) v) * 1 := mul_le_mul_right (h2 v) _
        _ = _ := mul_one _
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hO.prod hB')

/- English proof (translation)
Establish `hl : Continuous fun p : GL (Fin n) (Af E) × AfQˣ => (p.1.val.map (conjFin (GlobalTheory.SplitPts.conjE E)))ᵀ * p.1.val` using `((Units.continuous_val.comp continuous_fst).matrix_map (continuous_conjFin _)).matrix_transpose.matrix_mul (Units.continuous_val.comp continuous_fst)`. Establish `hr : Continuous fun p : GL (Fin n) (Af E) × AfQˣ => GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ) • (1 : Matrix (Fin n) (Fin n) (Af E))` using `Continuous.smul (f := fun p : GL (Fin n) (Af E) × AfQˣ => GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ)) (g := fun _ => (1 : Matrix (Fin n) (Fin n) (Af E))) (GroundTheory.Global.AdeleBaseChange.continuous_finiteAdeleMap.comp (Units.continuous_val.comp continu …`. Conclude with `isClosed_eq hl hr`.
-/
private theorem isClosed_GUf (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    IsClosed (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) := by
  have hl : Continuous fun p : GL (Fin n) (Af E) × AfQˣ =>
      (p.1.val.map (conjFin (GlobalTheory.SplitPts.conjE E)))ᵀ * p.1.val :=
    ((Units.continuous_val.comp continuous_fst).matrix_map (continuous_conjFin _)).matrix_transpose.matrix_mul
      (Units.continuous_val.comp continuous_fst)
  have hr : Continuous fun p : GL (Fin n) (Af E) × AfQˣ =>
      GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ) • (1 : Matrix (Fin n) (Fin n) (Af E)) :=
    Continuous.smul (f := fun p : GL (Fin n) (Af E) × AfQˣ => GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ))
      (g := fun _ => (1 : Matrix (Fin n) (Fin n) (Af E)))
      (GroundTheory.Global.AdeleBaseChange.continuous_finiteAdeleMap.comp (Units.continuous_val.comp continuous_snd))
      continuous_const
  exact isClosed_eq hl hr

/- English proof (translation)
Introduce `E _ _ _ n`. Rewrite using `[Topology.IsEmbedding.subtypeVal.isCompact_iff]`. Establish `e : Subtype.val '' (lev (E` using `E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n)) = (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) ∩ ((GlobalTheory.EulerTw.Kglob E n : Set _) ×ˢ (ZU : Set AfQˣ)) := by`. Use extensionality with `p`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨k, hk, rfl⟩`. Take `⟨h1, -, h3⟩` from `mem_lev.1 hk`. Conclude with `⟨k.2, GlobalTheory.EulerTwRestr.mem_Kglob.2 fun w => h3 w (by simp) (by simp), h1⟩`. Introduce and unpack `⟨hp, h1, h2⟩`. Use `⟨⟨p, hp⟩, mem_lev.2 ⟨h2, by simp, fun w _ _ => GlobalTheory.EulerTwRestr.mem_Kglob.1 h1 w⟩, rfl⟩` and prove the remaining obligations.

Rewrite using `[e]`. Conclude with `((GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)).prod isCompact_ZU).inter_left (isClosed_GUf E n)`.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.pIntCompact_of :
    UpperTheory.Gal.CertificateRingHomMap.IntCompact := by
  intro E _ _ _ n
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have e : Subtype.val '' (lev (E := E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n)) =
      (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) ∩ ((GlobalTheory.EulerTw.Kglob E n : Set _) ×ˢ (ZU : Set AfQˣ)) := by
    ext p
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨h1, -, h3⟩ := mem_lev.1 hk
      exact ⟨k.2, GlobalTheory.EulerTwRestr.mem_Kglob.2 fun w => h3 w (by simp) (by simp), h1⟩
    · rintro ⟨hp, h1, h2⟩
      refine ⟨⟨p, hp⟩, mem_lev.2 ⟨h2, by simp, fun w _ _ => GlobalTheory.EulerTwRestr.mem_Kglob.1 h1 w⟩, rfl⟩
  rw [e]
  exact ((GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)).prod isCompact_ZU).inter_left (isClosed_GUf E n)
