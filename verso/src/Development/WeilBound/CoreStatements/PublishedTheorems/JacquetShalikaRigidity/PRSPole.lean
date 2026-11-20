import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PRSPole

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Introduce `w a`. Establish `hu : (CG.mk π).IsUnitary` using `(CG.isUnitary_mk π).2 (GlobalTheory.Published.CuspFormsBoundedGL.isUnitary GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL hπ)`. Establish `h` using `(hJS E m (CG.mk π) hu w.1 _ (hα w) (α w a) (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2`. Use `show ‖((α w a : ℂˣ) : ℂ)‖ ≤ Real.sqrt ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)`. Rewrite using `[Real.sqrt_eq_rpow]`.

Conclude with `h.le`.
-/
theorem bnd (hJS : GlobalTheory.Published.JacquetShalikaBound) {m : ℕ} (π : CuspSub E m) (hπ : IsNormalised π)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (α : Off E S → Fin m → ℂˣ) (hα : SatOff (CG.mk π) S α) :
    ∀ w a, ‖(α w a : ℂ)‖ ≤ Real.sqrt (nq w) := by
  intro w a
  have hu : (CG.mk π).IsUnitary :=
    (CG.isUnitary_mk π).2 (GlobalTheory.Published.CuspFormsBoundedGL.isUnitary GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL hπ)
  have h := (hJS E m (CG.mk π) hu w.1 _ (hα w) (α w a)
    (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2
  show ‖((α w a : ℂˣ) : ℂ)‖ ≤ Real.sqrt ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)
  rw [Real.sqrt_eq_rpow]
  exact h.le

end PRSPole

open Classical in
/- English proof (translation)
Introduce `hJS _hG1 hG10 hW0 hE2 hM1 hKIR hKSec hK5e hKLt1 hKLt2 hK11 hKEq1 hKEq2 hORT hKY E _ _ _ m k π π' u hk hkm hπ hπ'`. Take `⟨ψ, hψ, hcond⟩` from `hG10 E`. Establish `hm : 1 ≤ m` using `hk.trans hkm`. Take `⟨S₁, hS₁⟩` from `hKSec E k hk ψ hψ hcond π' hπ'`. Take `⟨S₂, hS₂⟩` from `hKIR E m hm ψ hψ hcond π hπ`.

Use `⟨S₁ ∪ S₂, fun S hS α β hα hβ => ?_⟩` and prove the remaining obligations. Establish `hS1 : S₁ ⊆ S` using `Finset.union_subset_left hS`. Establish `hS2 : S₂ ⊆ S` using `Finset.union_subset_right hS`. Take `⟨hCond, hsec⟩` from `hS₁ S hS1`. Take `⟨φ₀', hφ₀', h', φ', hφ'e, hsec⟩` from `hsec β hβ`.

Establish `hαb` using `PRSPole.bnd hJS π hπ S α hα`. Establish `hβb` using `PRSPole.bnd hJS π' hπ' S β hβ`. Set `μ : Measure (GA E k)` to `Measure.haar`. Take `⟨⟨b, hb⟩, -⟩` from `hW0 E k μ hk`. Break down `hkm.lt_or_eq with hlt | heq` into its components or cases.

Take `⟨ι, hι⟩` from `((hK5e E m k hkm).1 (Ad E))`. Take `⟨U, hU, hUd⟩` from `hKLt1 E m k hk hlt ψ hψ S hCond ι hι α β u φ' hsec`. Take `⟨φ, -, hprep⟩` from `hS₂ S hS2 α hα (m ^ 3) k hlt U hU ⊤ isClosed_univ (fun _ _ _ => trivial) (fun _ _ => trivial)`. Establish `hdat` using `hUd (m ^ 3) (Nat.one_le_pow _ _ hm) φ hprep`. Establish `hgrow` using `hKLt2 E m k hk hlt ψ hψ S hCond ι hι α β φ' hsec U φ hprep`.

Take `⟨Z, hZd, hZe, hZ1⟩` from `hE2 E k μ hk b hb _ _ hgrow`. Take `⟨ZS, σ₀, hZSd, hZS0, hZSe⟩` from `hM1 E k μ hk b hb ψ hψ S m α β u _ _ hkm hαb hβb hdat`. Use `⟨Z, ZS, max 1 σ₀, hZd, hZSd.differentiableOn, fun σ _ => hZS0 σ, fun s hs => ?_, fun _ => hZ1 ?_⟩` and prove the remaining obligations. Rewrite using `[hZe s (lt_of_le_of_lt (le_max_left _ _) hs), hZSe s (lt_of_le_of_lt (le_max_right _ _) hs), mul_assoc]`. Simplify using the standard rewrite rules.

Substitute `heq` using the available equality. Take `⟨U, hU, hUd⟩` from `hKEq1 E k hk ψ hψ S hCond α β u φ' hsec`. Set `φ'' : XB E k` to `if π = π' then 0 else φ'`. Take `⟨Y, hYc, hYi, hYm, hYz⟩` from `hKY E k μ hk b hb φ''`. Establish `hforms : ∀ x : XB E k, (∃ φ ∈ π.V, (x : GA E k → ℂ) = φ.1) → x ∈ Y`.

Introduce and unpack `x ⟨φ₁, hφ₁, hx⟩`. Establish `hx' : ∀ g, x g = φ₁.1 g` using `congrFun hx`. Use `(hYm x).2 ⟨fun t g => by rw [hx', hx']; exact hπ φ₁ hφ₁ t g, fun h => ?_⟩` and prove the remaining obligations. Distinguish the cases in `he : π = π'`. Establish `e0 : φ'' = 0` using `if_pos he`.

Rewrite using `[e0]`. Simplify using the standard rewrite rules. Establish `e1 : φ'' = φ'` using `if_neg he`. Establish `hO` using `hORT E k μ hk b hb π π' hπ hπ' he φ₁ hφ₁ φ₀' hφ₀' h h'`. Rewrite using `[e1]`.

Simplify using `only [hx', hφ'e]`. Conclude with `hO`. Take `⟨φ, hφY, hprep⟩` from `hS₂ S hS2 α hα (k + 1) (k - 1) (by omega) U hU Y hYc hYi hforms`. Take `⟨η, s, hcut⟩` from `hK11 E k hk ψ hψ S hCond U hU φ hprep.smooth hprep.lev`. Establish `hdat` using `hUd φ hprep η s hcut`.

Establish `hcen` using `((hYm φ).1 hφY).1`. Establish `hgrow` using `hKEq2 E k hk ψ hψ S β φ' hsec U φ η s hcut hprep.inv hcen`. Take `⟨Z, hZd, hZe, hZ1⟩` from `hE2 E k μ hk b hb _ _ hgrow`. Take `⟨ZS, σ₀, hZSd, hZS0, hZSe⟩` from `hM1 E k μ hk b hb ψ hψ S k α β u _ _ le_rfl hαb hβb hdat`. Use `⟨Z, ZS, max 1 σ₀, hZd, hZSd.differentiableOn, fun σ _ => hZS0 σ, fun s hs => ?_, fun hne => hZ1 ?_⟩` and prove the remaining obligations.

Rewrite using `[hZe s (lt_of_le_of_lt (le_max_left _ _) hs), hZSe s (lt_of_le_of_lt (le_max_right _ _) hs), mul_assoc]`. Establish `hne' : π ≠ π'` using `fun e => hne (by rw [e])`. Establish `e1 : φ'' = φ'` using `if_neg hne'`. Establish `hz` using `hYz φ hφY ψ S U η s hcut`. Rewrite `hz` using `[e1]`.

Conclude with `hz`.
-/
theorem rspole_of : GlobalTheory.Published.JacquetShalikaBound → jumpWindows.G1 → jumpWindows.StandardCharacterExists → W0 → E2 → M1 → KIR → KSec → CornerEmbedding → KLt1 → KLt2 → LastRowCutoff → KEq1 → KEq2 → ORT → KY → RSPole := by
  intro hJS _hG1 hG10 hW0 hE2 hM1 hKIR hKSec hK5e hKLt1 hKLt2 hK11 hKEq1 hKEq2 hORT hKY E _ _ _ m k π π' u hk
    hkm hπ hπ'
  obtain ⟨ψ, hψ, hcond⟩ := hG10 E
  have hm : 1 ≤ m := hk.trans hkm
  obtain ⟨S₁, hS₁⟩ := hKSec E k hk ψ hψ hcond π' hπ'
  obtain ⟨S₂, hS₂⟩ := hKIR E m hm ψ hψ hcond π hπ
  refine ⟨S₁ ∪ S₂, fun S hS α β hα hβ => ?_⟩
  have hS1 : S₁ ⊆ S := Finset.union_subset_left hS
  have hS2 : S₂ ⊆ S := Finset.union_subset_right hS
  obtain ⟨hCond, hsec⟩ := hS₁ S hS1
  obtain ⟨φ₀', hφ₀', h', φ', hφ'e, hsec⟩ := hsec β hβ
  have hαb := PRSPole.bnd hJS π hπ S α hα
  have hβb := PRSPole.bnd hJS π' hπ' S β hβ
  let μ : Measure (GA E k) := Measure.haar
  obtain ⟨⟨b, hb⟩, -⟩ := hW0 E k μ hk
  rcases hkm.lt_or_eq with hlt | heq
  · obtain ⟨ι, hι⟩ := ((hK5e E m k hkm).1 (Ad E))
    obtain ⟨U, hU, hUd⟩ := hKLt1 E m k hk hlt ψ hψ S hCond ι hι α β u φ' hsec
    obtain ⟨φ, -, hprep⟩ := hS₂ S hS2 α hα (m ^ 3) k hlt U hU ⊤ isClosed_univ (fun _ _ _ => trivial)
      (fun _ _ => trivial)
    have hdat := hUd (m ^ 3) (Nat.one_le_pow _ _ hm) φ hprep
    have hgrow := hKLt2 E m k hk hlt ψ hψ S hCond ι hι α β φ' hsec U φ hprep
    obtain ⟨Z, hZd, hZe, hZ1⟩ := hE2 E k μ hk b hb _ _ hgrow
    obtain ⟨ZS, σ₀, hZSd, hZS0, hZSe⟩ := hM1 E k μ hk b hb ψ hψ S m α β u _ _ hkm hαb hβb hdat
    refine ⟨Z, ZS, max 1 σ₀, hZd, hZSd.differentiableOn, fun σ _ => hZS0 σ, fun s hs => ?_, fun _ => hZ1 ?_⟩
    · rw [hZe s (lt_of_le_of_lt (le_max_left _ _) hs), hZSe s (lt_of_le_of_lt (le_max_right _ _) hs), mul_assoc]
    · simp
  · subst heq
    obtain ⟨U, hU, hUd⟩ := hKEq1 E k hk ψ hψ S hCond α β u φ' hsec
    let φ'' : XB E k := if π = π' then 0 else φ'
    obtain ⟨Y, hYc, hYi, hYm, hYz⟩ := hKY E k μ hk b hb φ''
    have hforms : ∀ x : XB E k, (∃ φ ∈ π.V, (x : GA E k → ℂ) = φ.1) → x ∈ Y := by
      rintro x ⟨φ₁, hφ₁, hx⟩
      have hx' : ∀ g, x g = φ₁.1 g := congrFun hx
      refine (hYm x).2 ⟨fun t g => by rw [hx', hx']; exact hπ φ₁ hφ₁ t g, fun h => ?_⟩
      by_cases he : π = π'
      · have e0 : φ'' = 0 := if_pos he
        rw [e0]
        simp
      · have e1 : φ'' = φ' := if_neg he
        have hO := hORT E k μ hk b hb π π' hπ hπ' he φ₁ hφ₁ φ₀' hφ₀' h h'
        rw [e1]
        simp only [hx', hφ'e]
        exact hO
    obtain ⟨φ, hφY, hprep⟩ := hS₂ S hS2 α hα (k + 1) (k - 1) (by omega) U hU Y hYc hYi hforms
    obtain ⟨η, s, hcut⟩ := hK11 E k hk ψ hψ S hCond U hU φ hprep.smooth hprep.lev
    have hdat := hUd φ hprep η s hcut
    have hcen := ((hYm φ).1 hφY).1
    have hgrow := hKEq2 E k hk ψ hψ S β φ' hsec U φ η s hcut hprep.inv hcen
    obtain ⟨Z, hZd, hZe, hZ1⟩ := hE2 E k μ hk b hb _ _ hgrow
    obtain ⟨ZS, σ₀, hZSd, hZS0, hZSe⟩ := hM1 E k μ hk b hb ψ hψ S k α β u _ _ le_rfl hαb hβb hdat
    refine ⟨Z, ZS, max 1 σ₀, hZd, hZSd.differentiableOn, fun σ _ => hZS0 σ, fun s hs => ?_, fun hne => hZ1 ?_⟩
    · rw [hZe s (lt_of_le_of_lt (le_max_left _ _) hs), hZSe s (lt_of_le_of_lt (le_max_right _ _) hs), mul_assoc]
    · have hne' : π ≠ π' := fun e => hne (by rw [e])
      have e1 : φ'' = φ' := if_neg hne'
      have hz := hYz φ hφY ψ S U η s hcut
      rw [e1] at hz
      exact hz

end PositivityTheory.AdelicQuotientData

end
