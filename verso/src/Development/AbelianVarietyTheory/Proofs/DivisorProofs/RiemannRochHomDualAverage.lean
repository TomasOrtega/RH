import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharHomAdditiveShortExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiHomModAddOfGenRankEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsheafOfStructureTorsionQuotientStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option autoImplicit false

namespace GlobalTheory.RRDev

/- English proof (translation)
Introduce `k _ T _ _ hT E r hE F hF`. Establish `hfc : ∀ (G : T.Modules), QCoh.IsFiniteQC G → FiniteCoh k G` using `fun G _ => finiteCoh_of_isProjOver (algebraMap_eq_strHom k T) G hT.isProjOver`. Establish `hadd : ∀ (S : ShortComplex T.Modules), S.ShortExact → QCoh.IsFiniteQC S.X₁ → QCoh.IsFiniteQC S.X₂ → QCoh.IsFiniteQC S.X₃ → ((chi k (homMod (dual E) S.X₂) : ℚ) + (chi k (homMod E S.X₂) : ℚ)) / 2 - (r : ℚ) * (chi k S.X₂ : ℚ) = (((chi k (homMod (dual E) S.X₁) : ℚ) + (chi k (homMod E …`. Introduce `S hS h₁ h₂ h₃`. Establish `a` using `GlobalTheory.T.euler_char_hom_additive_short_exact k T hT (dual E) r hE.dual S hS h₁ h₂ h₃`.

Establish `b` using `GlobalTheory.T.euler_char_hom_additive_short_exact k T hT E r hE S hS h₁ h₂ h₃`. Establish `c` using `chi_shortExact hS (hfc _ h₁) (hfc _ h₃)`. Rewrite using `[a, b, c]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hO : QCoh.IsFiniteQC (structureModule T)` using `(isVB_structureModule T).isFiniteQC`. Establish `hgO : genRank (structureModule T) = 1` using `(isVB_structureModule T).genRank_eq`. Establish `hval : ((chi k (homMod (dual E) (structureModule T)) : ℚ) + (chi k (homMod E (structureModule T)) : ℚ)) / 2 - (r : ℚ) * (chi k (structureModule T) : ℚ) = degCh2 k E`. Use `hE.isIso_toBidual_of_local_frames` as an intermediate fact. Rewrite using `[degCh2_eq hE, show homMod (dual E) (structureModule T) = dual (dual E) from rfl, show homMod E (structureModule T) = dual E from rfl, ← chi_congr k (asIso (cartierDualToBidual E)), add_comm]`.

Establish `htor : ∀ (G : T.Modules), QCoh.IsFiniteQC G → genRank G = 0 → ((chi k (homMod (dual E) G) : ℚ) + (chi k (homMod E G) : ℚ)) / 2 - (r : ℚ) * (chi k G : ℚ) = 0`. Introduce `G hG h0`. Use `GlobalTheory.T.euler_char_dual_torsion_formula k T hT E r hE G hG h0` as an intermediate fact. Establish `: ((chi k (homMod (dual E) G) : ℚ) + (chi k (homMod E G) : ℚ)) = 2 * (r : ℚ) * (chi k G : ℚ)`. Conclude with `this` after adjusting the coercions.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. It suffices to establish `H : ∀ n : ℕ, ∀ (G : T.Modules), QCoh.IsFiniteQC G → genRank G = n → ((chi k (homMod (dual E) G) : ℚ) + (chi k (homMod E G) : ℚ)) / 2 - (r : ℚ) * (chi k G : ℚ) = (n : ℚ) * degCh2 k E from H _ F hF rfl`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `G hG h0`. Rewrite using `[htor G hG h0]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `G hG hn`. Take `⟨M, f, g, hM, hf, hg, hcf⟩` from `GlobalTheory.T.subsheaf_of_structure_torsion_quotient k T hT G hG (by omega)`. Establish `hSf : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact` using `{ exact := ShortComplex.exact_cokernel f }`. Establish `hSg : (ShortComplex.mk g (cokernel.π g) (cokernel.condition g)).ShortExact` using `{ exact := ShortComplex.exact_cokernel g }`. Establish `hCf : QCoh.IsFiniteQC (cokernel f)` using `QCoh.IsFiniteQC.of_epi (cokernel.π f)`.

Establish `hCg : QCoh.IsFiniteQC (cokernel g)` using `QCoh.IsFiniteQC.of_epi (cokernel.π g)`. Establish `rf` using `genRank_shortExact hSf`. Establish `rg` using `genRank_shortExact hSg`. Simplify using `only at rf rg`. Establish `hM1 : genRank M = 1` using `by omega`.

Establish `hcg : genRank (cokernel g) = n` using `by omega`. Establish `e1` using `hadd _ hSf hM hO hCf`. Establish `e2` using `hadd _ hSg hM hG hCg`. Simplify using `only at e1 e2`. Rewrite `e1` using `[hval, htor _ hCf hcf]`.

Rewrite using `[e2, ih _ hCg hcg, ← e1.trans (add_zero _) |>.symm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_eq_genRank_mul_degCh2 : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ (E : T.Modules) (r : ℕ), IsVB E r → ∀ (F : T.Modules), QCoh.IsFiniteQC F → ((chi k (homMod (dual E) F) : ℚ) + (chi k (homMod E F) : ℚ)) / 2 - (r : ℚ) * (chi k F : ℚ) = (genRank F : ℚ) * degCh2 k E := by
  intro k _ T _ _ hT E r hE F hF
  have hfc : ∀ (G : T.Modules), QCoh.IsFiniteQC G → FiniteCoh k G := fun G _ =>
    finiteCoh_of_isProjOver (algebraMap_eq_strHom k T) G hT.isProjOver

  have hadd : ∀ (S : ShortComplex T.Modules), S.ShortExact → QCoh.IsFiniteQC S.X₁ →
      QCoh.IsFiniteQC S.X₂ → QCoh.IsFiniteQC S.X₃ →
      ((chi k (homMod (dual E) S.X₂) : ℚ) + (chi k (homMod E S.X₂) : ℚ)) / 2 - (r : ℚ) * (chi k S.X₂ : ℚ) =
      (((chi k (homMod (dual E) S.X₁) : ℚ) + (chi k (homMod E S.X₁) : ℚ)) / 2 - (r : ℚ) * (chi k S.X₁ : ℚ)) +
      (((chi k (homMod (dual E) S.X₃) : ℚ) + (chi k (homMod E S.X₃) : ℚ)) / 2 - (r : ℚ) * (chi k S.X₃ : ℚ)) := by
    intro S hS h₁ h₂ h₃
    have a := GlobalTheory.T.euler_char_hom_additive_short_exact k T hT (dual E) r hE.dual S hS h₁ h₂ h₃
    have b := GlobalTheory.T.euler_char_hom_additive_short_exact k T hT E r hE S hS h₁ h₂ h₃
    have c := chi_shortExact hS (hfc _ h₁) (hfc _ h₃)
    rw [a, b, c]
    push_cast
    ring
  have hO : QCoh.IsFiniteQC (structureModule T) := (isVB_structureModule T).isFiniteQC
  have hgO : genRank (structureModule T) = 1 := (isVB_structureModule T).genRank_eq

  have hval : ((chi k (homMod (dual E) (structureModule T)) : ℚ) + (chi k (homMod E (structureModule T)) : ℚ)) / 2
      - (r : ℚ) * (chi k (structureModule T) : ℚ) = degCh2 k E := by
    have := hE.isIso_toBidual_of_local_frames
    rw [degCh2_eq hE, show homMod (dual E) (structureModule T) = dual (dual E) from rfl,
      show homMod E (structureModule T) = dual E from rfl, ← chi_congr k (asIso (cartierDualToBidual E)), add_comm]

  have htor : ∀ (G : T.Modules), QCoh.IsFiniteQC G → genRank G = 0 →
      ((chi k (homMod (dual E) G) : ℚ) + (chi k (homMod E G) : ℚ)) / 2 - (r : ℚ) * (chi k G : ℚ) = 0 := by
    intro G hG h0
    have := GlobalTheory.T.euler_char_dual_torsion_formula k T hT E r hE G hG h0
    have : ((chi k (homMod (dual E) G) : ℚ) + (chi k (homMod E G) : ℚ)) = 2 * (r : ℚ) * (chi k G : ℚ) := by
      exact_mod_cast this
    rw [this]; ring
  suffices H : ∀ n : ℕ, ∀ (G : T.Modules), QCoh.IsFiniteQC G → genRank G = n →
      ((chi k (homMod (dual E) G) : ℚ) + (chi k (homMod E G) : ℚ)) / 2 - (r : ℚ) * (chi k G : ℚ) =
        (n : ℚ) * degCh2 k E from H _ F hF rfl
  intro n
  induction n with
  | zero =>
    intro G hG h0
    rw [htor G hG h0]; simp
  | succ n ih =>
    intro G hG hn
    obtain ⟨M, f, g, hM, hf, hg, hcf⟩ := GlobalTheory.T.subsheaf_of_structure_torsion_quotient k T hT G hG (by omega)
    have hSf : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_cokernel f }
    have hSg : (ShortComplex.mk g (cokernel.π g) (cokernel.condition g)).ShortExact :=
      { exact := ShortComplex.exact_cokernel g }
    have hCf : QCoh.IsFiniteQC (cokernel f) := QCoh.IsFiniteQC.of_epi (cokernel.π f)
    have hCg : QCoh.IsFiniteQC (cokernel g) := QCoh.IsFiniteQC.of_epi (cokernel.π g)
    have rf := genRank_shortExact hSf
    have rg := genRank_shortExact hSg
    simp only at rf rg
    have hM1 : genRank M = 1 := by omega
    have hcg : genRank (cokernel g) = n := by omega
    have e1 := hadd _ hSf hM hO hCf
    have e2 := hadd _ hSg hM hG hCg
    simp only at e1 e2
    rw [hval, htor _ hCf hcf] at e1
    rw [e2, ih _ hCg hcg, ← e1.trans (add_zero _) |>.symm]
    push_cast; ring

end GlobalTheory.RRDev
