import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.LinearSubstitutionDiagonal
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (IsReps opU sumU fixedBy semicharacterHom)
open Formalism.L2.Col (Fields Sp HomE IsSdLat)
open Formalism.L2.Ker (Amb VCx LamC BC AC HV alV embH volC repsOf xiInd xiS hatS indL)

/- English proof (translation)
Introduce `X A a b S N N' c x hN hN' hLa hc hvol m₁ m₂ hcop hkill S₁ S₂ h1 h2 z`. Take `⟨-, -, -, -, hall⟩` from `Formalism.L2.Ker.heisHyp_of A a b S hLa`. Take `⟨hfix, hcc⟩` from `hall N N' hN hN'`. Take `⟨hsplit, hi1, hi2, -⟩` from `hcc c hc`. Take `⟨hH, -, hB, -, -, -⟩` from `hsplit`.

Establish `hSA` using `Formalism.L2.Ker.repsOf_spec _ _ hi1`. Establish `hSB` using `Formalism.L2.Ker.repsOf_spec _ _ hi2`. Use `set H : Formalism.L2.Th1.H.Sesq (VCx X.Tau a b) := HV A.sc with hHdef`. Use `set α : VCx X.Tau a b → ℂ := alV A.d A.sc with hαdef`. Use `set Λ := LamC (X.embC A.σ₀) A.δ A.AA N N' with hΛdef`.

Use `set B := BC (X.embC A.σ₀) A.δ A.AA S N N' c with hBdef`. Use `set SA := repsOf B (Λ ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c) with hSAdef`. Use `set SB := repsOf Λ B with hSBdef`. Use `set e := A.e a b N N' with hedef`. Use `set s := embH (X.embC A.σ₀) A.δ (A.liftW S N N' c x) with hsdef`.

Use `set vol := volC A.AA S N N' with hvoldef`. Establish `hsplitSum : ∀ w, (∑ y ∈ SB, α y * opU H y e w) = ∑ y ∈ S₁, α y * opU H y (sumU H α S₂ e) w`. Introduce `w`. Take `⟨hI, hinj⟩` from `KerA.image_reps B Λ m₁ m₂ hcop hkill S₁ S₂ h1 h2`. Establish `hinv : ∀ x ∈ B, ∀ m ∈ B, m ∈ Λ → α (x + m) * opU H (x + m) e w = α x * opU H x e w`.

Introduce `x hx m hmB hmΛ`. Rewrite using `[← semicharacterHom _ H hH B α hB x hx m hmB e w]`. Use `congr 2`. Use function extensionality and compare the values at `v`. Conclude with `hfix m hmΛ v`.

Rewrite using `[Formalism.L2.Ker.sum_reps_eq hSB hI (fun y => α y * opU H y e w) hinv, Finset.sum_image (fun q hq q' hq' h => hinj hq hq' h), Finset.sum_product]`. Use `Finset.sum_congr rfl fun y₁ hy₁ => ?_` and prove the remaining obligations. Establish `hsU : sumU H α S₂ e = fun v => ∑ y₂ ∈ S₂, α y₂ * opU H y₂ e v` using `rfl`. Rewrite using `[hsU, Formalism.L2.Th1.H.Inv.opU_finset_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun y₂ hy₂ => ?_` and prove the remaining obligations.

Establish `hy₁B : y₁ ∈ B` using `(KerA.mem_killIn.1 (h1.1 y₁ hy₁)).1`. Establish `hy₂B : y₂ ∈ B` using `(KerA.mem_killIn.1 (h2.1 y₂ hy₂)).1`. Conclude with `(semicharacterHom _ H hH B α hB y₁ hy₁B y₂ hy₂B e w).symm`. Establish `hxiS : xiS H α vol SA SB (indL B) e = fun w => (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ))) * ∑ y ∈ SB, α y * opU H y e w`. Use function extensionality and compare the values at `w`.

Simplify using `only [xiS, sumU]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Rewrite using `[Formalism.L2.Ker.hatS_ind H hH α B _ hB vol SA hSA (hSB.1 y hy)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hth : A.thInd S N N' c x z = ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiInd H α vol B SA SB e s z` using `rfl`. Rewrite using `[hth]`. Simplify using `only [xiInd]`. Rewrite using `[hxiS, Formalism.L2.Th1.H.Inv.opU_const_mul]`. Establish `hF : (fun w => ∑ y ∈ SB, α y * opU H y e w) = fun w => ∑ y ∈ S₁, α y * opU H y (sumU H α S₂ e) w`.

Use function extensionality and compare the values at `hsplitSum`. Rewrite using `[hF, Formalism.L2.Th1.H.Inv.opU_finset_sum]`. Establish `hT : ∑ i ∈ S₁, opU H (-s) (fun w => α i * opU H i (sumU H α S₂ e) w) z = ∑ y ∈ S₁, α y * opU H (-s) (opU H y (sumU H α S₂ e)) z`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Conclude with `Formalism.L2.Th1.H.Inv.opU_const_mul H (-s) (α y) _ z`.

Rewrite using `[hT]`. Use `set T := ∑ y ∈ S₁, α y * opU H (-s) (opU H y (sumU H α S₂ e)) z`. Use `set r : ℂ := ((Real.sqrt vol : ℝ) : ℂ) with hr`. Establish `hr0 : r ≠ 0`. Rewrite using `[hr]`.

Conclude with `(Real.sqrt_pos.2 hvol).ne'` after adjusting the coercions. Establish `hrr : r * r = ((vol : ℝ) : ℂ)`. Rewrite using `[hr, ← Complex.ofReal_mul, Real.mul_self_sqrt hvol.le]`. Establish `h1' : r⁻¹ * (α s * (r⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ)) * T)) = (r⁻¹ * r⁻¹ * (r * r)) * ((SA.card : ℂ)⁻¹ * α s * T)`. Rewrite using `[hrr]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2' : r⁻¹ * r⁻¹ * (r * r) = 1` using `by field_simp`. Rewrite using `[h1', h2', one_mul]`.
-/
theorem kernel_index_form : KerIndForm := by
  intro X A a b S N N' c x hN hN' hLa hc hvol m₁ m₂ hcop hkill S₁ S₂ h1 h2 z
  classical
  obtain ⟨-, -, -, -, hall⟩ := Formalism.L2.Ker.heisHyp_of A a b S hLa
  obtain ⟨hfix, hcc⟩ := hall N N' hN hN'
  obtain ⟨hsplit, hi1, hi2, -⟩ := hcc c hc
  obtain ⟨hH, -, hB, -, -, -⟩ := hsplit
  have hSA := Formalism.L2.Ker.repsOf_spec _ _ hi1
  have hSB := Formalism.L2.Ker.repsOf_spec _ _ hi2
  set H : Formalism.L2.Th1.H.Sesq (VCx X.Tau a b) := HV A.sc with hHdef
  set α : VCx X.Tau a b → ℂ := alV A.d A.sc with hαdef
  set Λ := LamC (X.embC A.σ₀) A.δ A.AA N N' with hΛdef
  set B := BC (X.embC A.σ₀) A.δ A.AA S N N' c with hBdef
  set SA := repsOf B (Λ ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c) with hSAdef
  set SB := repsOf Λ B with hSBdef
  set e := A.e a b N N' with hedef
  set s := embH (X.embC A.σ₀) A.δ (A.liftW S N N' c x) with hsdef
  set vol := volC A.AA S N N' with hvoldef

  have hsplitSum : ∀ w, (∑ y ∈ SB, α y * opU H y e w) = ∑ y ∈ S₁, α y * opU H y (sumU H α S₂ e) w := by
    intro w
    obtain ⟨hI, hinj⟩ := KerA.image_reps B Λ m₁ m₂ hcop hkill S₁ S₂ h1 h2
    have hinv : ∀ x ∈ B, ∀ m ∈ B, m ∈ Λ → α (x + m) * opU H (x + m) e w = α x * opU H x e w := by
      intro x hx m hmB hmΛ
      rw [← semicharacterHom _ H hH B α hB x hx m hmB e w]
      congr 2
      funext v
      exact hfix m hmΛ v
    rw [Formalism.L2.Ker.sum_reps_eq hSB hI (fun y => α y * opU H y e w) hinv,
      Finset.sum_image (fun q hq q' hq' h => hinj hq hq' h), Finset.sum_product]
    refine Finset.sum_congr rfl fun y₁ hy₁ => ?_
    have hsU : sumU H α S₂ e = fun v => ∑ y₂ ∈ S₂, α y₂ * opU H y₂ e v := rfl
    rw [hsU, Formalism.L2.Th1.H.Inv.opU_finset_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y₂ hy₂ => ?_
    have hy₁B : y₁ ∈ B := (KerA.mem_killIn.1 (h1.1 y₁ hy₁)).1
    have hy₂B : y₂ ∈ B := (KerA.mem_killIn.1 (h2.1 y₂ hy₂)).1
    exact (semicharacterHom _ H hH B α hB y₁ hy₁B y₂ hy₂B e w).symm

  have hxiS : xiS H α vol SA SB (indL B) e =
      fun w => (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ))) * ∑ y ∈ SB, α y * opU H y e w := by
    funext w
    simp only [xiS, sumU]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Formalism.L2.Ker.hatS_ind H hH α B _ hB vol SA hSA (hSB.1 y hy)]
    ring
  have hth : A.thInd S N N' c x z = ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiInd H α vol B SA SB e s z := rfl
  rw [hth]
  simp only [xiInd]
  rw [hxiS, Formalism.L2.Th1.H.Inv.opU_const_mul]
  have hF : (fun w => ∑ y ∈ SB, α y * opU H y e w) = fun w => ∑ y ∈ S₁, α y * opU H y (sumU H α S₂ e) w :=
    funext hsplitSum
  rw [hF, Formalism.L2.Th1.H.Inv.opU_finset_sum]
  have hT : ∑ i ∈ S₁, opU H (-s) (fun w => α i * opU H i (sumU H α S₂ e) w) z =
      ∑ y ∈ S₁, α y * opU H (-s) (opU H y (sumU H α S₂ e)) z := by
    refine Finset.sum_congr rfl fun y _ => ?_
    exact Formalism.L2.Th1.H.Inv.opU_const_mul H (-s) (α y) _ z
  rw [hT]
  set T := ∑ y ∈ S₁, α y * opU H (-s) (opU H y (sumU H α S₂ e)) z
  set r : ℂ := ((Real.sqrt vol : ℝ) : ℂ) with hr
  have hr0 : r ≠ 0 := by
    rw [hr]; exact_mod_cast (Real.sqrt_pos.2 hvol).ne'
  have hrr : r * r = ((vol : ℝ) : ℂ) := by
    rw [hr, ← Complex.ofReal_mul, Real.mul_self_sqrt hvol.le]
  have h1' : r⁻¹ * (α s * (r⁻¹ * (((vol : ℝ) : ℂ) / (SA.card : ℂ)) * T)) =
      (r⁻¹ * r⁻¹ * (r * r)) * ((SA.card : ℂ)⁻¹ * α s * T) := by
    rw [hrr]; ring
  have h2' : r⁻¹ * r⁻¹ * (r * r) = 1 := by field_simp
  rw [h1', h2', one_mul]

end Formalism.L2.AlgTh
