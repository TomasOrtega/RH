import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.SUCong

namespace GlobalTheory.FrameDual

open ReciprocityTheory.ChartRestriction.G.FD

/- English proof (translation)
Simplify using `only [herm, Matrix.vecMul, dotProduct, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem herm_eq_dot {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = (x ᵥ* G) ⬝ᵥ (fun b => cc (y b)) := by
  simp only [herm, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Use `set σ : E →+* E := ((IsCMField.complexConj E).toAlgHom : E →+* E)`. Rewrite using `[herm_eq_dot]`. Establish `h1 : (fun b => cc ((P *ᵥ z) b)) = (P.map σ) *ᵥ (fun k => cc (z k))`. Use function extensionality and compare the values at `b`. Conclude with `RingHom.map_mulVec σ P z b`.

Rewrite using `[h1, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose P w, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.vecMul_transpose]`. Use `congr 2`. Simplify using `[Formalism.UG.cT, Matrix.transpose_mul, Matrix.mul_assoc, σ]`.
-/
theorem herm_mulVec {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G P : Matrix (Fin r) (Fin r) E) (w z : Fin r → E) :
    herm G (P *ᵥ w) (P *ᵥ z) =
      ((Formalism.UG.cT ((IsCMField.complexConj E).toAlgHom : E →+* E) P * Gᵀ * P) *ᵥ w) ⬝ᵥ
        (fun k => cc (z k)) := by
  set σ : E →+* E := ((IsCMField.complexConj E).toAlgHom : E →+* E)
  rw [herm_eq_dot]
  have h1 : (fun b => cc ((P *ᵥ z) b)) = (P.map σ) *ᵥ (fun k => cc (z k)) := by
    funext b
    exact RingHom.map_mulVec σ P z b
  rw [h1, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose P w, Matrix.vecMul_vecMul,
    Matrix.vecMul_vecMul, ← Matrix.vecMul_transpose]
  congr 2
  simp [Formalism.UG.cT, Matrix.transpose_mul, Matrix.mul_assoc, σ]

/- English proof (translation)
Simplify using `only [GlobalTheory.AdelicU.stdLattice, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range, Algebra.linearMap_apply]`. Use `forall_congr' fun i => ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Rewrite using `[← hy]`. Conclude with `y.isIntegral_coe`.

Introduce `h`. Conclude with `⟨⟨x i, h⟩, rfl⟩`.
-/
theorem memStd {E : Type} [Field E] {r : ℕ} {x : Fin r → E} :
    x ∈ GlobalTheory.AdelicU.stdLattice E r ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp only [GlobalTheory.AdelicU.stdLattice, Formalism.UG.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies,
    LinearMap.mem_range, Algebra.linearMap_apply]
  refine forall_congr' fun i => ⟨?_, ?_⟩
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact y.isIntegral_coe
  · intro h
    exact ⟨⟨x i, h⟩, rfl⟩

/- English proof (translation)
The claim follows from `s.isIntegral_coe.algebraMap`.
-/
theorem int_coe {E : Type} [Field E] [NumberField E] [IsCMField E]
    (s : 𝓞 (maximalRealSubfield E)) :
    IsIntegral ℤ (algebraMap (maximalRealSubfield E) E s) :=
  s.isIntegral_coe.algebraMap

/- English proof (translation)
The claim follows from `(IsCMField.complexConj_eq_self_iff E _).2 (s : maximalRealSubfield E).2`.
-/
theorem cc_coe {E : Type} [Field E] [NumberField E] [IsCMField E]
    (s : 𝓞 (maximalRealSubfield E)) :
    cc (algebraMap (maximalRealSubfield E) E s) = algebraMap (maximalRealSubfield E) E s :=
  (IsCMField.complexConj_eq_self_iff E _).2 (s : maximalRealSubfield E).2

/- English proof (translation)
The claim follows from `h.map ((IsCMField.complexConj E).toAlgHom : E →+* E).toIntAlgHom`.
-/
theorem int_cc {E : Type} [Field E] [NumberField E] [IsCMField E] {x : E}
    (h : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  h.map ((IsCMField.complexConj E).toAlgHom : E →+* E).toIntAlgHom

end GlobalTheory.FrameDual

namespace GlobalTheory.FrameDual

open ReciprocityTheory.ChartRestriction.G.FD

/- English proof (translation)
Establish `hz : (fun k => cc ((b • Pi.single i 1 : Fin r → E) k)) = Pi.single i b`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[hb]`.

Simplify using `[hk, cc]`. Rewrite using `[hz, dotProduct_single, Matrix.mulVec_smul, Matrix.mulVec_single_one]`. Simplify using `[smul_eq_mul]`.
-/
theorem dot_single {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) E) (a b : E) (hb : cc b = b) (i j : Fin r) :
    (M *ᵥ (a • Pi.single j 1)) ⬝ᵥ (fun k => cc ((b • Pi.single i 1 : Fin r → E) k)) = a * M i j * b := by
  have hz : (fun k => cc ((b • Pi.single i 1 : Fin r → E) k)) = Pi.single i b := by
    funext k
    by_cases hk : k = i
    · subst hk; simp [hb]
    · simp [hk, cc]
  rw [hz, dotProduct_single, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  simp [smul_eq_mul]

/- English proof (translation)
Take `⟨si, hsi, hPi⟩` from `h1 i`. Take `⟨sj, hsj, hPj⟩` from `h1 j`. Use `⟨sj * si, fun h => (v.isPrime.mem_or_mem h).elim hsj hsi, ?_⟩` and prove the remaining obligations. Establish `hcol : ∀ (c : E) (k : Fin r), (c • fun i => P i k) = P *ᵥ (c • Pi.single k 1)`. Introduce `c k`.

Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Establish `hint` using `(hΛ.2.2.2.2 _).2 hPj _ hPi`. Rewrite `hint` using `[hcol, hcol, herm_mulVec, dot_single _ _ _ (cc_coe si)]`. Use `hint using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem part1 {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} (hΛ : SelfDualLat G Λ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : Matrix (Fin r) (Fin r) E)
    (h1 : ∀ j, ∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧
      (algebraMap (maximalRealSubfield E) E s • fun i => P i j) ∈ Λ) (i j : Fin r) :
    ∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap (maximalRealSubfield E) E s *
      (Formalism.UG.cT ((IsCMField.complexConj E).toAlgHom : E →+* E) P * Gᵀ * P) i j) := by
  obtain ⟨si, hsi, hPi⟩ := h1 i
  obtain ⟨sj, hsj, hPj⟩ := h1 j
  refine ⟨sj * si, fun h => (v.isPrime.mem_or_mem h).elim hsj hsi, ?_⟩
  have hcol : ∀ (c : E) (k : Fin r), (c • fun i => P i k) = P *ᵥ (c • Pi.single k 1) := by
    intro c k
    rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
    rfl
  have hint := (hΛ.2.2.2.2 _).2 hPj _ hPi
  rw [hcol, hcol, herm_mulVec, dot_single _ _ _ (cc_coe si)] at hint
  convert hint using 1
  push_cast
  ring

end GlobalTheory.FrameDual

namespace GlobalTheory.FrameDual

open ReciprocityTheory.ChartRestriction.G.FD

/- English proof (translation)
Take `⟨S, hS⟩` from `hFG`. Establish `hmem : ∀ g ∈ S, ∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧ algebraMap (maximalRealSubfield E) E s • Q *ᵥ g ∈ GlobalTheory.AdelicU.stdLattice E r` using `fun g hg => h2 g (hS ▸ Submodule.subset_span hg)`. Use `choose sf hsf hsfm using hmem`. Use `⟨∏ g ∈ S.attach, sf g.1 g.2, ?_, ?_⟩` and prove the remaining obligations. Introduce `h haveI := v.isPrime`.

Take `⟨g, -, hg⟩` from `Ideal.IsPrime.prod_mem_iff.1 h`. Conclude with `hsf g.1 g.2 hg`. Use `set c : E := algebraMap (maximalRealSubfield E) E ((∏ g ∈ S.attach, sf g.1 g.2 : 𝓞 (maximalRealSubfield E)) : maximalRealSubfield E) with hc`. Set `T : Submodule (𝓞 E) (Fin r → E)` to `{ carrier := {y | ∀ k, IsIntegral ℤ (c * (Q *ᵥ y) k)} add_mem' := by`. Introduce `a b ha hb k`.

Simplify using `only [Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply, mul_add] at *`. Conclude with `(ha k).add (hb k)`. Use the proof step `zero_mem' := by`. Introduce `k`. Simplify using `[isIntegral_zero]`.

Use the proof step `smul_mem' := by`. Introduce `a y hy k`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[← algebraMap_smul E a y, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]`. Conclude with `a.isIntegral_coe.mul (hy k) }`.

Establish `hle : Submodule.span (𝓞 E) (S : Set (Fin r → E)) ≤ T`. Rewrite using `[Submodule.span_le]`. Introduce `g hg k`. Establish `hsplit : c = algebraMap (maximalRealSubfield E) E ((∏ h ∈ S.attach.erase ⟨g, hg⟩, sf h.1 h.2 : 𝓞 (maximalRealSubfield E)) : maximalRealSubfield E) * algebraMap (maximalRealSubfield E) E (sf g hg)`. Rewrite using `[hc, ← Finset.prod_erase_mul _ _ (Finset.mem_attach S ⟨g, hg⟩)]`.

Move the coercions through the operations in `[map_mul]`. Both sides reduce to the same expression. Establish `h3` using `(memStd.1 (hsfm g hg)) k`. Rewrite `h3` using `[Pi.smul_apply, smul_eq_mul]`. Use `show IsIntegral ℤ (c * (Q *ᵥ g) k)`.

Rewrite using `[hsplit, mul_assoc]`. Conclude with `(int_coe _).mul h3`. Introduce `y hy k`. Conclude with `hle (hS ▸ hy) k`.
-/
theorem uniform {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hFG : Λ.FG)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (Q : Matrix (Fin r) (Fin r) E)
    (h2 : ∀ x ∈ Λ, ∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧
      algebraMap (maximalRealSubfield E) E s • Q *ᵥ x ∈ GlobalTheory.AdelicU.stdLattice E r) :
    ∃ s₀ : 𝓞 (maximalRealSubfield E), s₀ ∉ v.asIdeal ∧
      ∀ y ∈ Λ, ∀ k, IsIntegral ℤ (algebraMap (maximalRealSubfield E) E s₀ * (Q *ᵥ y) k) := by
  classical
  obtain ⟨S, hS⟩ := hFG
  have hmem : ∀ g ∈ S, ∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧
      algebraMap (maximalRealSubfield E) E s • Q *ᵥ g ∈ GlobalTheory.AdelicU.stdLattice E r :=
    fun g hg => h2 g (hS ▸ Submodule.subset_span hg)
  choose sf hsf hsfm using hmem
  refine ⟨∏ g ∈ S.attach, sf g.1 g.2, ?_, ?_⟩
  · intro h
    haveI := v.isPrime
    obtain ⟨g, -, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hsf g.1 g.2 hg
  · set c : E := algebraMap (maximalRealSubfield E) E
      ((∏ g ∈ S.attach, sf g.1 g.2 : 𝓞 (maximalRealSubfield E)) : maximalRealSubfield E) with hc
    let T : Submodule (𝓞 E) (Fin r → E) :=
      { carrier := {y | ∀ k, IsIntegral ℤ (c * (Q *ᵥ y) k)}
        add_mem' := by
          intro a b ha hb k
          simp only [Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply, mul_add] at *
          exact (ha k).add (hb k)
        zero_mem' := by
          intro k
          simp [isIntegral_zero]
        smul_mem' := by
          intro a y hy k
          simp only [Set.mem_setOf_eq] at *
          rw [← algebraMap_smul E a y, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
            mul_left_comm]
          exact a.isIntegral_coe.mul (hy k) }
    have hle : Submodule.span (𝓞 E) (S : Set (Fin r → E)) ≤ T := by
      rw [Submodule.span_le]
      intro g hg k
      have hsplit : c = algebraMap (maximalRealSubfield E) E
          ((∏ h ∈ S.attach.erase ⟨g, hg⟩, sf h.1 h.2 : 𝓞 (maximalRealSubfield E)) :
            maximalRealSubfield E) *
          algebraMap (maximalRealSubfield E) E (sf g hg) := by
        rw [hc, ← Finset.prod_erase_mul _ _ (Finset.mem_attach S ⟨g, hg⟩)]
        push_cast [map_mul]
        rfl
      have h3 := (memStd.1 (hsfm g hg)) k
      rw [Pi.smul_apply, smul_eq_mul] at h3
      show IsIntegral ℤ (c * (Q *ᵥ g) k)
      rw [hsplit, mul_assoc]
      exact (int_coe _).mul h3
    intro y hy k
    exact hle (hS ▸ hy) k

end GlobalTheory.FrameDual

namespace GlobalTheory.FrameDual

open ReciprocityTheory.ChartRestriction.G.FD

/- English proof (translation)
Use `set Pm : Matrix (Fin r) (Fin r) E := (P : Matrix (Fin r) (Fin r) E) with hPm`. Use `set Q : Matrix (Fin r) (Fin r) E := ((P⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hQ`. Use `set σ : E →+* E := ((IsCMField.complexConj E).toAlgHom : E →+* E) with hσ`. Use `set H := Formalism.UG.cT σ Pm * Gᵀ * Pm with hH`. Establish `hPQ : Pm * Q = 1` using `Units.mul_inv P`.

Establish `hQP : Q * Pm = 1` using `Units.inv_mul P`. Establish `hP : Pm.det ≠ 0`. Use `congrArg Matrix.det hPQ` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `left_ne_zero_of_mul_eq_one this`.

Establish `hdet : H.det ≠ 0`. Establish `hm : (Pm.map σ).det = σ Pm.det` using `by rw [RingHom.map_det]; rfl`. Rewrite using `[hH, Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, Matrix.det_transpose, hm]`. Conclude with `mul_ne_zero (mul_ne_zero ((map_ne_zero σ).2 hP) hΛ.2.1) hP`. Take `⟨s₀, hs₀, hU⟩` from `uniform hΛ.2.2.1 v Q h2`.

Use `set c₀ : E := algebraMap (maximalRealSubfield E) E s₀ with hc₀`. Use `set w : Fin r → E := H⁻¹ *ᵥ Pi.single j 1 with hw`. Establish `hHw : H *ᵥ w = Pi.single j 1`. Rewrite using `[hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]`. Use `set x : Fin r → E := Pm *ᵥ (c₀ • w) with hx`.

Establish `hxΛ : x ∈ Λ`. Use `(hΛ.2.2.2.2 x).1 fun y hy => ?_` and prove the remaining obligations. Establish `hy' : y = Pm *ᵥ (Q *ᵥ y)` using `by rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]`. Establish `e1 : herm G x y = herm G (Pm *ᵥ (c₀ • w)) (Pm *ᵥ (Q *ᵥ y))` using `by rw [← hy']`. Rewrite using `[e1, herm_mulVec, Matrix.mulVec_smul, hHw, smul_dotProduct, single_dotProduct, one_mul, smul_eq_mul]`.

Establish `e : cc (c₀ * (Q *ᵥ y) j) = c₀ * cc ((Q *ᵥ y) j)`. Unfold `cc`. Rewrite using `[map_mul]`. Use `congr 1`. Conclude with `cc_coe s₀`.

Rewrite using `[← e]`. Conclude with `int_cc (hU y hy j)`. Take `⟨s', hs', hmem⟩` from `h2 x hxΛ`. Establish `hQx : Q *ᵥ x = c₀ • w` using `by rw [hx, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]`. Establish `hI` using `memStd.1 hmem i`.

Rewrite `hI` using `[hQx, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]`. Establish `hwi : w i = H⁻¹ i j`. Rewrite using `[hw, Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Use `⟨s' * s₀, fun h => (v.isPrime.mem_or_mem h).elim hs' hs₀, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hwi]`. Use `hI using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hc₀]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem part2 {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} (hΛ : SelfDualLat G Λ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : GL (Fin r) E)
    (h2 : ∀ x ∈ Λ, ∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧
      algebraMap (maximalRealSubfield E) E s • ((P⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x ∈
        GlobalTheory.AdelicU.stdLattice E r) (i j : Fin r) :
    ∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap (maximalRealSubfield E) E s *
      (Formalism.UG.cT ((IsCMField.complexConj E).toAlgHom : E →+* E) (P : Matrix (Fin r) (Fin r) E) * Gᵀ *
        (P : Matrix (Fin r) (Fin r) E))⁻¹ i j) := by
  set Pm : Matrix (Fin r) (Fin r) E := (P : Matrix (Fin r) (Fin r) E) with hPm
  set Q : Matrix (Fin r) (Fin r) E := ((P⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hQ
  set σ : E →+* E := ((IsCMField.complexConj E).toAlgHom : E →+* E) with hσ
  set H := Formalism.UG.cT σ Pm * Gᵀ * Pm with hH
  have hPQ : Pm * Q = 1 := Units.mul_inv P
  have hQP : Q * Pm = 1 := Units.inv_mul P
  have hP : Pm.det ≠ 0 := by
    have := congrArg Matrix.det hPQ
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hdet : H.det ≠ 0 := by
    have hm : (Pm.map σ).det = σ Pm.det := by rw [RingHom.map_det]; rfl
    rw [hH, Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, Matrix.det_transpose, hm]
    exact mul_ne_zero (mul_ne_zero ((map_ne_zero σ).2 hP) hΛ.2.1) hP
  obtain ⟨s₀, hs₀, hU⟩ := uniform hΛ.2.2.1 v Q h2
  set c₀ : E := algebraMap (maximalRealSubfield E) E s₀ with hc₀
  set w : Fin r → E := H⁻¹ *ᵥ Pi.single j 1 with hw
  have hHw : H *ᵥ w = Pi.single j 1 := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  set x : Fin r → E := Pm *ᵥ (c₀ • w) with hx
  have hxΛ : x ∈ Λ := by
    refine (hΛ.2.2.2.2 x).1 fun y hy => ?_
    have hy' : y = Pm *ᵥ (Q *ᵥ y) := by rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
    have e1 : herm G x y = herm G (Pm *ᵥ (c₀ • w)) (Pm *ᵥ (Q *ᵥ y)) := by rw [← hy']
    rw [e1, herm_mulVec, Matrix.mulVec_smul, hHw, smul_dotProduct, single_dotProduct, one_mul,
      smul_eq_mul]
    have e : cc (c₀ * (Q *ᵥ y) j) = c₀ * cc ((Q *ᵥ y) j) := by
      unfold cc
      rw [map_mul]
      congr 1
      exact cc_coe s₀
    rw [← e]
    exact int_cc (hU y hy j)
  obtain ⟨s', hs', hmem⟩ := h2 x hxΛ
  have hQx : Q *ᵥ x = c₀ • w := by rw [hx, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  have hI := memStd.1 hmem i
  rw [hQx, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at hI
  have hwi : w i = H⁻¹ i j := by
    rw [hw, Matrix.mulVec_single_one]
    rfl
  refine ⟨s' * s₀, fun h => (v.isPrime.mem_or_mem h).elim hs' hs₀, ?_⟩
  rw [← hwi]
  convert hI using 1
  rw [hc₀]
  push_cast
  ring

end GlobalTheory.FrameDual

/- English proof (translation)
Introduce `E _ _ _ r G Λ hΛ v P h1 h2 i j`. Conclude with `⟨GlobalTheory.FrameDual.part1 hΛ v (P : Matrix (Fin r) (Fin r) E) h1 i j, GlobalTheory.FrameDual.part2 hΛ v P h2 i j⟩`.
-/
theorem GlobalTheory.FrameDual.gram_integral_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), SelfDualLat G Λ → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : GL (Fin r) E), (∀ j, ∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧ (algebraMap (maximalRealSubfield E) E s • fun i => (P : Matrix (Fin r) (Fin r) E) i j) ∈ Λ) → (∀ x ∈ Λ, ∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧ algebraMap (maximalRealSubfield E) E s • ((P⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ GlobalTheory.AdelicU.stdLattice E r) → ∀ (i j : Fin r), (∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap (maximalRealSubfield E) E s * (Formalism.UG.cT ((IsCMField.complexConj E).toAlgHom : E →+* E) (P : Matrix (Fin r) (Fin r) E) * Gᵀ * (P : Matrix (Fin r) (Fin r) E)) i j)) ∧ (∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap (maximalRealSubfield E) E s * (Formalism.UG.cT ((IsCMField.complexConj E).toAlgHom : E →+* E) (P : Matrix (Fin r) (Fin r) E) * Gᵀ * (P : Matrix (Fin r) (Fin r) E))⁻¹ i j)) := by
  intro E _ _ _ r G Λ hΛ v P h1 h2 i j
  exact ⟨GlobalTheory.FrameDual.part1 hΛ v (P : Matrix (Fin r) (Fin r) E) h1 i j, GlobalTheory.FrameDual.part2 hΛ v P h2 i j⟩
