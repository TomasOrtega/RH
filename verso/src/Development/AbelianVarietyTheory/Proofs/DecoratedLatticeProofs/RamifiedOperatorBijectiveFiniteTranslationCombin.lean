import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RamBij

variable {D : D7}

def contAutSub (S : HSp D) : Submodule ℂ (GA D S → ℂ) where
  carrier := {φ | IsContAut S φ}
  add_mem' ha hb := ⟨fun γ hγ g => by simp [ha.1 γ hγ g, hb.1 γ hγ g], ha.2.add hb.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' c φ h := ⟨fun γ hγ g => by simp [h.1 γ hγ g], h.2.const_smul c⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Use function extensionality and compare the values at `P₁`. Establish `h` using `Classical.epsilon_spec (p := fun g : GL n k => g • P = P₁) (MulAction.exists_smul_eq (GL n k) P P₁)`. Use `show β.rep _ (φ P) = φ P₁`. Rewrite using `[← hφ, h]`.
-/
theorem formAt_eq (β : Frame p S n) (P : Pair k n) {φ : Form k n (GA D S → ℂ)} (hφ : φ ∈ EqForm β.rep) :
    formAt β P (φ P) = φ := by
  funext P₁
  have h := Classical.epsilon_spec (p := fun g : GL n k => g • P = P₁) (MulAction.exists_smul_eq (GL n k) P P₁)
  show β.rep _ (φ P) = φ P₁
  rw [← hφ, h]

/- English proof (translation)
Rewrite using `[← Finsupp.sum_finset_sum_index (fun h => zero_smul ℂ (β.rep h φ₀)) (fun h _ _ => add_smul _ _ (β.rep h φ₀))]`. Conclude with `Finset.sum_congr rfl fun i _ => Finsupp.sum_single_index (zero_smul ℂ _)`.
-/
theorem sum_single_sum (β : Frame p S n) {ι : Type} (s : Finset ι) (g : ι → GL n k) (a : ι → ℂ)
    (φ₀ : GA D S → ℂ) :
    (∑ i ∈ s, Finsupp.single (g i) (a i)).sum (fun h b => b • β.rep h φ₀) = ∑ i ∈ s, a i • β.rep (g i) φ₀ := by
  rw [← Finsupp.sum_finset_sum_index (fun h => zero_smul ℂ (β.rep h φ₀)) (fun h _ _ => add_smul _ _ (β.rep h φ₀))]
  exact Finset.sum_congr rfl fun i _ => Finsupp.sum_single_index (zero_smul ℂ _)

section Ops

variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (β : Frame p S n)

/- English proof (translation)
Use `⟨dia_mem_EqForm ε (FFStar_mem_EqForm q χ hφ.1), hO.dia_mem_ram ε _ (hO.FFStar_mem_ram _ hφ.2.1), fun P' => ?_⟩` and prove the remaining obligations. Rewrite using `[dia_apply, FFStar_apply]`. Conclude with `(contAutSub S).sum_mem fun P₁ _ => (contAutSub S).smul_mem _ (hφ.2.2 P₁)`.
-/
theorem isRam_diaFFStar (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ : Form k n (GA D S → ℂ)}
    (hφ : IsRam β φ) : IsRam β (dia ε (FFStar q χ φ)) := by
  refine ⟨dia_mem_EqForm ε (FFStar_mem_EqForm q χ hφ.1), hO.dia_mem_ram ε _ (hO.FFStar_mem_ram _ hφ.2.1),
    fun P' => ?_⟩
  rw [dia_apply, FFStar_apply]
  exact (contAutSub S).sum_mem fun P₁ _ => (contAutSub S).smul_mem _ (hφ.2.2 P₁)

/- English proof (translation)
Use `⟨(EqForm β.rep).smul_mem c (FF_mem_EqForm q χ (dia_mem_EqForm _ hφ.1)), (Mram k n _).smul_mem c (hO.FF_mem_ram _ (hO.dia_mem_ram _ _ hφ.2.1)), fun P' => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, FF_apply]`. Use `(contAutSub S).smul_mem c ((contAutSub S).sum_mem fun Q _ => (contAutSub S).smul_mem _ ?_)` and prove the remaining obligations. Rewrite using `[dia_apply]`. Conclude with `hφ.2.2 _`.
-/
theorem isRam_FFdia (hO : OperatorIdentities k n (GA D S → ℂ) q χ) (c : ℂ) {φ : Form k n (GA D S → ℂ)}
    (hφ : IsRam β φ) : IsRam β (c • FF q χ (dia ε⁻¹ φ)) := by
  refine ⟨(EqForm β.rep).smul_mem c (FF_mem_EqForm q χ (dia_mem_EqForm _ hφ.1)),
    (Mram k n _).smul_mem c (hO.FF_mem_ram _ (hO.dia_mem_ram _ _ hφ.2.1)), fun P' => ?_⟩
  rw [Pi.smul_apply, FF_apply]
  refine (contAutSub S).smul_mem c ((contAutSub S).sum_mem fun Q _ => (contAutSub S).smul_mem _ ?_)
  rw [dia_apply]
  exact hφ.2.2 _

/- English proof (translation)
Establish `hqr : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0` using `pow_ne_zero _ GlobalTheory.PairOp.resCard_ne_zero`. Rewrite using `[map_smul, map_smul, hO.FFStar_FF_ram _ (hO.dia_mem_ram _ _ h), map_smul, smul_smul, inv_mul_cancel₀ hqr, one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.
-/
theorem diaFFStar_inv (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ : Form k n (GA D S → ℂ)}
    (h : φ ∈ Mram k n (GA D S → ℂ)) :
    dia ε (FFStar q χ (((resCard k : ℂ) ^ Fintype.card n)⁻¹ • FF q χ (dia ε⁻¹ φ))) = φ := by
  have hqr : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ GlobalTheory.PairOp.resCard_ne_zero
  rw [map_smul, map_smul, hO.FFStar_FF_ram _ (hO.dia_mem_ram _ _ h), map_smul, smul_smul, inv_mul_cancel₀ hqr,
    one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Establish `hqr : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0` using `pow_ne_zero _ GlobalTheory.PairOp.resCard_ne_zero`. Establish `h2 : FF q χ (dia ε⁻¹ (dia ε (FFStar q χ φ))) = FF q χ (dia ε⁻¹ (dia ε (FFStar q χ φ')))` using `by rw [he]`. Establish `hd : ∀ X : Form k n (GA D S → ℂ), dia ε⁻¹ (dia ε X) = X` using `fun X => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Rewrite `h2` using `[hd, hd, hO.FF_FFStar_ram _ h, hO.FF_FFStar_ram _ h']`.

Conclude with `smul_right_injective _ hqr h2`.
-/
theorem diaFFStar_inj (hO : OperatorIdentities k n (GA D S → ℂ) q χ) {φ φ' : Form k n (GA D S → ℂ)}
    (h : φ ∈ Mram k n (GA D S → ℂ)) (h' : φ' ∈ Mram k n (GA D S → ℂ))
    (he : dia ε (FFStar q χ φ) = dia ε (FFStar q χ φ')) : φ = φ' := by
  have hqr : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ GlobalTheory.PairOp.resCard_ne_zero
  have h2 : FF q χ (dia ε⁻¹ (dia ε (FFStar q χ φ))) = FF q χ (dia ε⁻¹ (dia ε (FFStar q χ φ'))) := by rw [he]
  have hd : ∀ X : Form k n (GA D S → ℂ), dia ε⁻¹ (dia ε X) = X := fun X => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hd, hd, hO.FF_FFStar_ram _ h, hO.FF_FFStar_ram _ h'] at h2
  exact smul_right_injective _ hqr h2

end Ops

/- English proof (translation)
Use `set χ := resChar χ₀ hχ q with hχdef`. Establish `hO : OperatorIdentities k n (GA D S → ℂ) q χ` using `((GlobalTheory.PairOp.pairOperatorStatement k q χ₀ hχ n).1 (GA D S → ℂ)).2`. Use `set r : ℂ := ((resCard k : ℂ) ^ Fintype.card n)⁻¹ with hr`. Establish `hval : ∀ φ, IsRam β φ → sOp β P q χ ε (φ P) = dia ε (FFStar q χ φ) P` using `fun φ hφ => by show dia ε (FFStar q χ (formAt β P (φ P))) P = _`. Rewrite using `[formAt_eq β P hφ.1]`.

Establish `hinv : ∀ φ, IsRam β φ → sOp β P q χ ε ((r • FF q χ (dia ε⁻¹ φ)) P) = φ P` using `fun φ hφ => by`. Rewrite using `[hval _ (isRam_FFdia q χ ε β hO r hφ), diaFFStar_inv q χ ε hO hφ.2.1]`. Set `gch : Pair k n → GL n k` to `fun P₁ => Classical.epsilon fun g : GL n k => g • P = P₁`. Use `⟨⟨?_, ?_, ?_⟩, fun φ hφ => ⟨isRam_diaFFStar q χ ε β hO hφ, hval φ hφ⟩, ∑ P₁ ∈ withKer (ε • P).lat, Finsupp.single (gch P₁) (χ (-cross q P₁ (ε • P))), ∑ Q ∈ withLat P.ker, Finsupp.single (gch (ε⁻¹ • Q)) (r * χ (cross q P Q)), fun φ₀ => ?_, fun φ₀ hφ₀ => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`.

Conclude with `⟨_, isRam_diaFFStar q χ ε β hO hφ, (hval φ hφ).symm⟩`. Introduce and unpack `_ ⟨φ, hφ, rfl⟩ _ ⟨φ', hφ', rfl⟩ he`. Rewrite `he` using `[hval φ hφ, hval φ' hφ']`. Establish `hX` using `isRam_diaFFStar q χ ε β hO hφ`. Establish `hX'` using `isRam_diaFFStar q χ ε β hO hφ'`.

Establish `he' : dia ε (FFStar q χ φ) = dia ε (FFStar q χ φ')`. Rewrite using `[← formAt_eq β P hX.1, ← formAt_eq β P hX'.1, he]`. Rewrite using `[diaFFStar_inj q χ ε hO hφ.2.1 hφ'.2.1 he']`. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Conclude with `⟨_, ⟨_, isRam_FFdia q χ ε β hO r hφ, rfl⟩, hinv φ hφ⟩`.

Rewrite using `[sum_single_sum]`. Both sides reduce to the same expression. Take `⟨φ, hφ, rfl⟩` from `hφ₀`. Establish `hc : (∑ Q ∈ withLat P.ker, Finsupp.single (gch (ε⁻¹ • Q)) (r * χ (cross q P Q))).sum (fun g a => a • β.rep g (φ P)) = (r • FF q χ (dia ε⁻¹ φ)) P`. Rewrite using `[sum_single_sum, Pi.smul_apply, FF_apply, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun Q _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, dia_apply]`. Use `conv_rhs => rw [← formAt_eq β P hφ.1]`. Both sides reduce to the same expression. Rewrite using `[hc]`.

Conclude with `⟨hinv φ hφ, _, isRam_FFdia q χ ε β hO r hφ, rfl⟩`.
-/
theorem ramBijective_at (q : Unif k) (χ₀ : AddChar k Circle) (hχ : HasConductor χ₀ 1) (ε : 𝓀[k]ˣ)
    (β : Frame p S n) (P : Pair k n) :
    Set.BijOn (sOp β P q (resChar χ₀ hχ q) ε) {φ₀ | RamAt β P φ₀} {φ₀ | RamAt β P φ₀} ∧
      (∀ φ, IsRam β φ → IsRam β (dia ε (FFStar q (resChar χ₀ hχ q) φ)) ∧
        sOp β P q (resChar χ₀ hχ q) ε (φ P) = dia ε (FFStar q (resChar χ₀ hχ q) φ) P) ∧
      ∃ c c' : GL n k →₀ ℂ, (∀ φ₀, sOp β P q (resChar χ₀ hχ q) ε φ₀ = c.sum fun g a => a • β.rep g φ₀) ∧
        ∀ φ₀, RamAt β P φ₀ → sOp β P q (resChar χ₀ hχ q) ε (c'.sum fun g a => a • β.rep g φ₀) = φ₀ ∧
          RamAt β P (c'.sum fun g a => a • β.rep g φ₀) := by
  set χ := resChar χ₀ hχ q with hχdef
  have hO : OperatorIdentities k n (GA D S → ℂ) q χ :=
    ((GlobalTheory.PairOp.pairOperatorStatement k q χ₀ hχ n).1 (GA D S → ℂ)).2
  set r : ℂ := ((resCard k : ℂ) ^ Fintype.card n)⁻¹ with hr

  have hval : ∀ φ, IsRam β φ → sOp β P q χ ε (φ P) = dia ε (FFStar q χ φ) P := fun φ hφ => by
    show dia ε (FFStar q χ (formAt β P (φ P))) P = _
    rw [formAt_eq β P hφ.1]

  have hinv : ∀ φ, IsRam β φ → sOp β P q χ ε ((r • FF q χ (dia ε⁻¹ φ)) P) = φ P := fun φ hφ => by
    rw [hval _ (isRam_FFdia q χ ε β hO r hφ), diaFFStar_inv q χ ε hO hφ.2.1]
  let gch : Pair k n → GL n k := fun P₁ => Classical.epsilon fun g : GL n k => g • P = P₁
  refine ⟨⟨?_, ?_, ?_⟩, fun φ hφ => ⟨isRam_diaFFStar q χ ε β hO hφ, hval φ hφ⟩,
    ∑ P₁ ∈ withKer (ε • P).lat, Finsupp.single (gch P₁) (χ (-cross q P₁ (ε • P))),
    ∑ Q ∈ withLat P.ker, Finsupp.single (gch (ε⁻¹ • Q)) (r * χ (cross q P Q)), fun φ₀ => ?_, fun φ₀ hφ₀ => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨_, isRam_diaFFStar q χ ε β hO hφ, (hval φ hφ).symm⟩
  · rintro _ ⟨φ, hφ, rfl⟩ _ ⟨φ', hφ', rfl⟩ he
    rw [hval φ hφ, hval φ' hφ'] at he
    have hX := isRam_diaFFStar q χ ε β hO hφ
    have hX' := isRam_diaFFStar q χ ε β hO hφ'
    have he' : dia ε (FFStar q χ φ) = dia ε (FFStar q χ φ') := by
      rw [← formAt_eq β P hX.1, ← formAt_eq β P hX'.1, he]
    rw [diaFFStar_inj q χ ε hO hφ.2.1 hφ'.2.1 he']
  · rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨_, ⟨_, isRam_FFdia q χ ε β hO r hφ, rfl⟩, hinv φ hφ⟩
  · rw [sum_single_sum]
    rfl
  · obtain ⟨φ, hφ, rfl⟩ := hφ₀
    have hc : (∑ Q ∈ withLat P.ker, Finsupp.single (gch (ε⁻¹ • Q)) (r * χ (cross q P Q))).sum
        (fun g a => a • β.rep g (φ P)) = (r • FF q χ (dia ε⁻¹ φ)) P := by
      rw [sum_single_sum, Pi.smul_apply, FF_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun Q _ => ?_
      rw [smul_smul, dia_apply]
      conv_rhs => rw [← formAt_eq β P hφ.1]
      rfl
    rw [hc]
    exact ⟨hinv φ hφ, _, isRam_FFdia q χ ε β hO r hφ, rfl⟩

end GlobalTheory.FinPl.RamBij

namespace GlobalTheory.FinPl

/- English proof (translation)
Introduce `D k _ _ _ _ p n _ _ q χ₀ hχ χ hχeq ε S β P`. Substitute `hχeq` using the available equality. Conclude with `RamBij.ramBijective_at q χ₀ hχ ε β P`.
-/
theorem ramBijective_holds : ∀ D : D7, GlobalTheory.FinPl.RamBijective D := by
  intro D k _ _ _ _ p n _ _ q χ₀ hχ χ hχeq ε S β P
  subst hχeq
  exact RamBij.ramBijective_at q χ₀ hχ ε β P

end GlobalTheory.FinPl
