import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct

namespace GlobalTheory.SplitLocEq

open NumberField IsDedekindDomain TensorProduct in

/- English proof (translation)
Establish `h : (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) * _root_.ReciprocityTheory.Aut.conjT (_root_.ReciprocityTheory.Aut.conjAL L) (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) = 1` using `x.2`. Establish `hinv : _root_.ReciprocityTheory.Aut.conjT (_root_.ReciprocityTheory.Aut.conjAL L) (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) = (((x⁻¹ : _root_.ReciprocityTheory.Aut.GA L n).1 : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root …`. Establish `h'` using `congrArg (fun M => (((x.1)⁻¹ : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) * M) h`. Simplify `h'` using `[← mul_assoc]`. Rewrite using `[← hinv]`.

Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.SplitLocEq.conj_entry {L : Type} [Field L] [NumberField L] [IsCMField L]
    {n : ℕ} (x : _root_.ReciprocityTheory.Aut.GA L n) (i j : Fin n) :
    _root_.ReciprocityTheory.Aut.conjAL L ((x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
      (((x⁻¹ : _root_.ReciprocityTheory.Aut.GA L n).1 : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) j i := by
  have h : (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) *
      _root_.ReciprocityTheory.Aut.conjT (_root_.ReciprocityTheory.Aut.conjAL L) (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) = 1 := x.2
  have hinv : _root_.ReciprocityTheory.Aut.conjT (_root_.ReciprocityTheory.Aut.conjAL L) (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) =
      (((x⁻¹ : _root_.ReciprocityTheory.Aut.GA L n).1 : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) := by
    have h' := congrArg
      (fun M => (((x.1)⁻¹ : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) * M) h
    simpa [← mul_assoc] using h'
  rw [← hinv]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem proj_entry {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) (x : GA L n)
    (i j : Fin n) : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      ((s.loc n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := rfl

open NumberField IsDedekindDomain TensorProduct in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem evalAt_apply' {L : Type} [Field L] [NumberField L] (w)
    (a : _root_.ReciprocityTheory.Aut.AFplus L) : _root_.ReciprocityTheory.Aut.evalAt L w a = a w := rfl

open NumberField IsDedekindDomain TensorProduct in
/- English proof (translation)
Set `b : Module.Basis (Fin 2) (maximalRealSubfield L) L` to `Module.finBasisOfFinrankEq _ _ (Algebra.IsQuadraticExtension.finrank_eq_two _ _)`. Take `⟨a, c, rfl⟩` from `_root_.GlobalTheory.tensor_exists_decomp b d`. Establish `hw' : ∀ w, w ≠ s.v → a w = 0 ∧ c w = 0` using `fun w hne => _root_.GlobalTheory.tensor_decomp_eq_zero b _ _ (by simpa [_root_.ReciprocityTheory.Aut.compAt, evalAt_apply'] using hw w hne)`. Simplify using `only [map_add, _root_.ReciprocityTheory.Aut.SplitPlace.proj, _root_.ReciprocityTheory.Aut.conjAL] at h₁ h₂`. Simplify using `[evalAt_apply'] at h₁ h₂`.

Use `set σ := IsCMField.complexConj L`. Establish `hΔ : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) ≠ 0`. Introduce `h0`. Establish `h0' : b 0 * σ (b 1) - b 1 * σ (b 0) = 0` using `(injective_iff_map_eq_zero s.i.toRingHom).mp (RingHom.injective s.i.toRingHom) _ h0`. Establish `hb1 : b 1 ≠ 0` using `b.ne_zero 1`.

Establish `hσb1 : σ (b 1) ≠ 0` using `by simpa using hb1`. Establish `hfix : σ (b 0 / b 1) = b 0 / b 1`. Rewrite using `[map_div₀, div_eq_div_iff hσb1 hb1]`. Take the linear combination `-h0'`. Take `⟨k, hk⟩ : ∃ k : maximalRealSubfield L, (k : L) = b 0 / b 1` from `⟨⟨_, (IsCMField.complexConj_eq_self_iff L _).mp hfix⟩, rfl⟩`.

Establish `hsum : ∑ i, (![1, -k] : Fin 2 → maximalRealSubfield L) i • b i = 0`. Rewrite using `[Fin.sum_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]`. Establish `hsm : k • b 1 = (k : L) * b 1` using `rfl`. Rewrite using `[hsm, hk, div_mul_cancel₀ _ hb1]`.

Expand and normalize the polynomial expressions, which then agree. Use `Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum 0` as an intermediate fact. Simplify using `at this`. Establish `hA : a s.v = 0`. Establish `: s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) * a s.v = 0`.

Simplify using `only [map_sub, map_mul]`. Take the linear combination `s.i (σ (b 1)) * h₁ - s.i (b 1) * h₂`. Conclude with `(mul_eq_zero.mp this).resolve_left hΔ`. Establish `hC : c s.v = 0`. Establish `: s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) * c s.v = 0`.

Simplify using `only [map_sub, map_mul]`. Take the linear combination `s.i (b 0) * h₂ - s.i (σ (b 0)) * h₁`. Conclude with `(mul_eq_zero.mp this).resolve_left hΔ`. Establish `ha : a = 0`. Use extensionality with `w : 1`.

Distinguish the cases in `hv : w = s.v`. Substitute `hv` using the available equality. Conclude with `hA`. Conclude with `(hw' w hv).1`. Establish `hc : c = 0`.

Use extensionality with `w : 1`. Distinguish the cases in `hv : w = s.v`. Substitute `hv` using the available equality. Conclude with `hC`. Conclude with `(hw' w hv).2`.

Simplify using `[ha, hc]`.
-/
private theorem eq_zero_of_compAt_eq_zero_of_proj_conj_eq_zero {L : Type} [Field L] [NumberField L] [IsCMField L]
    (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (d : _root_.ReciprocityTheory.Aut.AL L)
    (hw : ∀ w, w ≠ s.v → _root_.ReciprocityTheory.Aut.compAt L w d = 0) (h₁ : s.proj d = 0)
    (h₂ : s.proj (_root_.ReciprocityTheory.Aut.conjAL L d) = 0) : d = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L :=
    Module.finBasisOfFinrankEq _ _ (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
  obtain ⟨a, c, rfl⟩ := _root_.GlobalTheory.tensor_exists_decomp b d
  have hw' : ∀ w, w ≠ s.v → a w = 0 ∧ c w = 0 := fun w hne =>
    _root_.GlobalTheory.tensor_decomp_eq_zero b _ _
      (by simpa [_root_.ReciprocityTheory.Aut.compAt, evalAt_apply'] using hw w hne)
  simp only [map_add, _root_.ReciprocityTheory.Aut.SplitPlace.proj, _root_.ReciprocityTheory.Aut.conjAL] at h₁ h₂
  simp [evalAt_apply'] at h₁ h₂
  set σ := IsCMField.complexConj L
  have hΔ : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) ≠ 0 := by
    intro h0
    have h0' : b 0 * σ (b 1) - b 1 * σ (b 0) = 0 :=
      (injective_iff_map_eq_zero s.i.toRingHom).mp (RingHom.injective s.i.toRingHom) _ h0
    have hb1 : b 1 ≠ 0 := b.ne_zero 1
    have hσb1 : σ (b 1) ≠ 0 := by simpa using hb1
    have hfix : σ (b 0 / b 1) = b 0 / b 1 := by
      rw [map_div₀, div_eq_div_iff hσb1 hb1]
      linear_combination -h0'
    obtain ⟨k, hk⟩ : ∃ k : maximalRealSubfield L, (k : L) = b 0 / b 1 :=
      ⟨⟨_, (IsCMField.complexConj_eq_self_iff L _).mp hfix⟩, rfl⟩
    have hsum : ∑ i, (![1, -k] : Fin 2 → maximalRealSubfield L) i • b i = 0 := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
      have hsm : k • b 1 = (k : L) * b 1 := rfl
      rw [hsm, hk, div_mul_cancel₀ _ hb1]
      ring
    have := Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum 0
    simp at this
  have hA : a s.v = 0 := by
    have : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) * a s.v = 0 := by
      simp only [map_sub, map_mul]
      linear_combination s.i (σ (b 1)) * h₁ - s.i (b 1) * h₂
    exact (mul_eq_zero.mp this).resolve_left hΔ
  have hC : c s.v = 0 := by
    have : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) * c s.v = 0 := by
      simp only [map_sub, map_mul]
      linear_combination s.i (b 0) * h₂ - s.i (σ (b 0)) * h₁
    exact (mul_eq_zero.mp this).resolve_left hΔ
  have ha : a = 0 := by
    ext w : 1
    by_cases hv : w = s.v
    · subst hv; exact hA
    · exact (hw' w hv).1
  have hc : c = 0 := by
    ext w : 1
    by_cases hv : w = s.v
    · subst hv; exact hC
    · exact (hw' w hv).2
  simp [ha, hc]

open NumberField IsDedekindDomain TensorProduct in

/- English proof (translation)
Introduce `L _ _ _ n s x y hx hy hxy`. Establish `triv : ∀ z : _root_.ReciprocityTheory.Aut.GA L n, _root_.ReciprocityTheory.Aut.TrivOutside {s.v} z → ∀ w, w ≠ s.v → ∀ i j, _root_.ReciprocityTheory.Aut.compAt L w ((z.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j`. Introduce `z hz w hw i j`. Use `hz w (by simpa using hw)` as an intermediate fact. Conclude with `congrFun (congrFun this i) j`.

Establish `trivInv : ∀ z : _root_.ReciprocityTheory.Aut.GA L n, _root_.ReciprocityTheory.Aut.TrivOutside {s.v} z → _root_.ReciprocityTheory.Aut.TrivOutside {s.v} z⁻¹`. Introduce `z hz w hw`. Use `show ((z⁻¹).1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)).map (_root_.ReciprocityTheory.Aut.compAt L w) = 1`. Establish `hm : (z.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) * ((z⁻¹).1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) = 1` using `by simp`. Establish `h2` using `congrArg (Matrix.map · (_root_.ReciprocityTheory.Aut.compAt L w)) hm`.

Simplify using `only [Matrix.map_mul] at h2`. Rewrite `h2` using `[hz w hw, one_mul]`. Rewrite using `[h2]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `hinv : s.loc n x⁻¹ = s.loc n y⁻¹` using `by simp [map_inv, hxy]`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_compAt_eq_zero_of_proj_conj_eq_zero s` to reduce the goal to its premises.

Introduce `w hw`. Rewrite using `[map_sub, triv x hx w hw, triv y hy w hw, sub_self]`. Rewrite using `[map_sub, _root_.GlobalTheory.SplitLocEq.proj_entry, _root_.GlobalTheory.SplitLocEq.proj_entry, hxy, sub_self]`. Rewrite using `[map_sub, _root_.GlobalTheory.SplitLocEq.conj_entry, _root_.GlobalTheory.SplitLocEq.conj_entry, map_sub, _root_.GlobalTheory.SplitLocEq.proj_entry, _root_.GlobalTheory.SplitLocEq.proj_entry, hinv, sub_self]`.
-/
theorem _root_.GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq : ∀ (L : Type) [Field L] [NumberField L]
    [IsCMField L] (n : ℕ) (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (x y : _root_.Formalism.AUTREP.GAf L n),
    _root_.ReciprocityTheory.Aut.TrivOutside {s.v} x → _root_.ReciprocityTheory.Aut.TrivOutside {s.v} y → s.loc n x = s.loc n y → x = y := by
  intro L _ _ _ n s x y hx hy hxy
  have triv : ∀ z : _root_.ReciprocityTheory.Aut.GA L n, _root_.ReciprocityTheory.Aut.TrivOutside {s.v} z → ∀ w, w ≠ s.v → ∀ i j,
      _root_.ReciprocityTheory.Aut.compAt L w ((z.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
        (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro z hz w hw i j
    have := hz w (by simpa using hw)
    exact congrFun (congrFun this i) j
  have trivInv : ∀ z : _root_.ReciprocityTheory.Aut.GA L n, _root_.ReciprocityTheory.Aut.TrivOutside {s.v} z → _root_.ReciprocityTheory.Aut.TrivOutside {s.v} z⁻¹ := by
    intro z hz w hw
    show ((z⁻¹).1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)).map (_root_.ReciprocityTheory.Aut.compAt L w) = 1
    have hm : (z.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) *
        ((z⁻¹).1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) = 1 := by simp
    have h2 := congrArg (Matrix.map · (_root_.ReciprocityTheory.Aut.compAt L w)) hm
    simp only [Matrix.map_mul] at h2
    rw [hz w hw, one_mul] at h2
    rw [h2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hinv : s.loc n x⁻¹ = s.loc n y⁻¹ := by simp [map_inv, hxy]
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_compAt_eq_zero_of_proj_conj_eq_zero s
  · intro w hw
    rw [map_sub, triv x hx w hw, triv y hy w hw, sub_self]
  · rw [map_sub, _root_.GlobalTheory.SplitLocEq.proj_entry, _root_.GlobalTheory.SplitLocEq.proj_entry, hxy, sub_self]
  · rw [map_sub, _root_.GlobalTheory.SplitLocEq.conj_entry, _root_.GlobalTheory.SplitLocEq.conj_entry,
      map_sub, _root_.GlobalTheory.SplitLocEq.proj_entry, _root_.GlobalTheory.SplitLocEq.proj_entry, hinv, sub_self]

end GlobalTheory.SplitLocEq
