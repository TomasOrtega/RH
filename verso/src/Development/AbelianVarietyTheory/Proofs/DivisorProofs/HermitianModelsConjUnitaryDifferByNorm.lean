import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReducedFreeAlgebraTraceFormPerfect
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

/- English proof (translation)
Establish `h1 : (cT (cj w) y.val) * 1 * y.val = 1` using `hy`. Establish `h2 : (y.val)ᵀ * y.val.map (cj w) = 1`. Use `congrArg Matrix.transpose h1` as an intermediate fact. Simplify `this` using `[cT, Matrix.transpose_mul]`. Establish `hs : ∀ z : Fin n → w.adicCompletion E, ∀ z', stdH w z z' = z ⬝ᵥ (fun k => cj w (z' k))`.

Introduce `z z'`. Both sides reduce to the same expression. Establish `hc : (fun k => cj w ((y.val *ᵥ v') k)) = y.val.map (cj w) *ᵥ (fun k => cj w (v' k))`. Use function extensionality and compare the values at `k`. Conclude with `RingHom.map_mulVec (cj w) y.val v' k`.

Rewrite using `[hs, hs, hc, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]`.
-/
theorem stdH_mulVec_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ)
    (y : GLw n w) (hy : y ∈ UJ (cj w) 1) (v v' : Fin n → w.adicCompletion E) :
    stdH w (y.val *ᵥ v) (y.val *ᵥ v') = stdH w v v' := by
  have h1 : (cT (cj w) y.val) * 1 * y.val = 1 := hy
  have h2 : (y.val)ᵀ * y.val.map (cj w) = 1 := by
    have := congrArg Matrix.transpose h1
    simpa [cT, Matrix.transpose_mul] using this
  have hs : ∀ z : Fin n → w.adicCompletion E, ∀ z', stdH w z z' = z ⬝ᵥ (fun k => cj w (z' k)) := by
    intro z z'; rfl
  have hc : (fun k => cj w ((y.val *ᵥ v') k)) = y.val.map (cj w) *ᵥ (fun k => cj w (v' k)) := by
    funext k; exact RingHom.map_mulVec (cj w) y.val v' k
  rw [hs, hs, hc, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, h2,
    Matrix.vecMul_one]

/- English proof (translation)
Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `ha`. Establish `hmem : a ∈ Algebra.adjoin F {u}` using `by rw [hu]; trivial`. Rewrite `hmem` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, rfl⟩` from `hmem`.

Establish `hsq : Squarefree (minpoly F u)` using `hP.squarefree_of_dvd (minpoly.dvd F u hPu)`. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases. Establish `h10 : (1 : A) = 0` using `by simpa using hk`. Conclude with `(subsingleton_of_zero_eq_one h10.symm).elim _ _`. Establish `hd : minpoly F u ∣ p ^ k` using `minpoly.dvd F u (by rw [map_pow]; exact hk)`.

Establish `hd' : minpoly F u ∣ p` using `(hsq.dvd_pow_iff_dvd hk0.ne').1 hd`. Take `⟨r, hr⟩` from `hd'`. Express the relevant statement in the definitionally equal form `aeval u p = 0`. Rewrite using `[hr, map_mul, minpoly.aeval, zero_mul]`.
-/
theorem isReduced_of_adjoin_squarefree {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (hu : Algebra.adjoin F {u} = ⊤) (P : F[X]) (hP : Squarefree P) (hPu : aeval u P = 0) :
    IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := ha
  have hmem : a ∈ Algebra.adjoin F {u} := by rw [hu]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, rfl⟩ := hmem
  have hsq : Squarefree (minpoly F u) := hP.squarefree_of_dvd (minpoly.dvd F u hPu)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  ·
    have h10 : (1 : A) = 0 := by simpa using hk
    exact (subsingleton_of_zero_eq_one h10.symm).elim _ _
  have hd : minpoly F u ∣ p ^ k := minpoly.dvd F u (by rw [map_pow]; exact hk)
  have hd' : minpoly F u ∣ p := (hsq.dvd_pow_iff_dvd hk0.ne').1 hd
  obtain ⟨r, hr⟩ := hd'
  change aeval u p = 0
  rw [hr, map_mul, minpoly.aeval, zero_mul]

/- English proof (translation)
Introduce `E _ _ _ w hw K e n Q B u x x' hQ hF γ y hy hM hM'`. Take `⟨hadj, hroot, -, -⟩` from `hF`. Establish `hyU : y ∈ UJ (cj w) 1` using `by simpa [UL, hw] using hy`. Take `⟨ψ, hψs, hψu, hψh⟩` from `hM`. Take `⟨ψ', hψs', hψu', hψh'⟩` from `hM'`.

Set `ψ₃ : B.A → (Fin n → w.adicCompletion E)` to `fun a => y.val *ᵥ ψ' a`. Establish `h3s : ∀ (c : K.E) (a : B.A), ψ₃ (c • a) = e c • ψ₃ a`. Introduce `c a`. Simplify using `only [ψ₃, hψs', Matrix.mulVec_smul]`. Establish `h3u : ∀ a, ψ₃ (u * a) = γ.val *ᵥ ψ₃ a`.

Introduce `a`. Simplify using `only [ψ₃, hψu', Matrix.mulVec_mulVec, Units.val_mul]`. Use `congr 1`. Rewrite using `[← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]`. Establish `h3h : ∀ a b, stdH w (ψ₃ a) (ψ₃ b) = e (B.herm x' a b)`.

Introduce `a b`. Simplify using `only [ψ₃]`. Rewrite using `[stdH_mulVec_of_mem w n y hyU, hψh']`. Set `φ : B.A → B.A` to `fun a => ψ.symm (ψ₃ a)`. Establish `hφψ : ∀ a, ψ (φ a) = ψ₃ a` using `fun a => ψ.apply_symm_apply _`.

Establish `hφs : ∀ (c : K.E) (a : B.A), φ (c • a) = c • φ a`. Introduce `c a`. Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[hψs, hφψ, hφψ, h3s]`. Establish `hφu : ∀ a, φ (u * a) = u * φ a`.

Introduce `a`. Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[hψu, hφψ, hφψ, h3u]`. Establish `hφadd : ∀ a b, φ (a + b) = φ a + φ b`. Introduce `a b`.

Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[map_add, hφψ, hφψ, hφψ]`. Simplify using `[ψ₃, Matrix.mulVec_add]`. Establish `hφmul : ∀ a b, φ (a * b) = a * φ b`. Introduce `a`.

Establish `ha : a ∈ Algebra.adjoin K.E {u}` using `by rw [hadj]; trivial`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem z hz`. Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality.

Conclude with `hφu`. Consider the case `algebraMap r`. Introduce `b`. Rewrite using `[← Algebra.smul_def, ← Algebra.smul_def, hφs]`. Consider the case `add a₁ a₂ _ _ h₁ h₂`.

Introduce `b`. Rewrite using `[add_mul, hφadd, h₁, h₂, add_mul]`. Consider the case `mul a₁ a₂ _ _ h₁ h₂`. Introduce `b`. Rewrite using `[mul_assoc, h₁, h₂, mul_assoc]`.

Establish `hφ : ∀ a, φ a = a * φ 1` using `fun a => by rw [← hφmul, mul_one]`. Choose the witnesses or unpack the hypotheses as in `⟨a₀, ha₀⟩ : ∃ a₀, φ a₀ = 1 := by`. Use `⟨ψ'.symm ((y⁻¹ : GLw n w).val *ᵥ ψ 1), ?_⟩` and prove the remaining obligations. Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[hφψ]`.

Simplify using `only [ψ₃, AddEquiv.apply_symm_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Set `c : B.Aˣ` to `⟨φ 1, a₀, by rw [mul_comm, ← hφ, ha₀], by rw [← hφ, ha₀]⟩`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hh : ∀ a b, B.herm x' a b = B.herm x (φ a) (φ b)`. Introduce `a b`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[← h3h, ← hψh, hφψ, hφψ]`. Establish `htr : ∀ z : B.A, Algebra.trace K.E B.A ((x * ((c : B.A) * B.σ (c : B.A)) - x') * z) = 0`. Introduce `z`. Use `hh z 1` as an intermediate fact.

Simplify using `only [GlobalTheory.UnitLemma.InvAlg.herm, map_one, mul_one] at this`. Rewrite `this` using `[hφ z]`. Establish `hc : (c : B.A) = φ 1` using `rfl`. Rewrite using `[hc, sub_mul, map_sub, sub_eq_zero, this]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `haveI : IsReduced B.A := isReduced_of_adjoin_squarefree u hadj _ (hQ.map.squarefree) hroot`. Conclude with `(sub_eq_zero.1 (GlobalTheory.RegSS.eq_zero_of_trace_mul_eq_zero _ htr)).symm`.
-/
theorem model_conj_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X])
    (B : GlobalTheory.UnitLemma.InvAlg K) (u x x' : B.A), Q.Separable → Fits w e B Q u →
    ∀ γ y : GLw n w, y ∈ UL n w → IsModel w e B u x γ → IsModel w e B u x' (y⁻¹ * γ * y) →
    ∃ c : B.Aˣ, x' = x * ((c : B.A) * B.σ (c : B.A)) := by
  intro E _ _ _ w hw K e n Q B u x x' hQ hF γ y hy hM hM'
  obtain ⟨hadj, hroot, -, -⟩ := hF
  have hyU : y ∈ UJ (cj w) 1 := by simpa [UL, hw] using hy
  obtain ⟨ψ, hψs, hψu, hψh⟩ := hM
  obtain ⟨ψ', hψs', hψu', hψh'⟩ := hM'

  let ψ₃ : B.A → (Fin n → w.adicCompletion E) := fun a => y.val *ᵥ ψ' a
  have h3s : ∀ (c : K.E) (a : B.A), ψ₃ (c • a) = e c • ψ₃ a := by
    intro c a; simp only [ψ₃, hψs', Matrix.mulVec_smul]
  have h3u : ∀ a, ψ₃ (u * a) = γ.val *ᵥ ψ₃ a := by
    intro a
    simp only [ψ₃, hψu', Matrix.mulVec_mulVec, Units.val_mul]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have h3h : ∀ a b, stdH w (ψ₃ a) (ψ₃ b) = e (B.herm x' a b) := by
    intro a b; simp only [ψ₃]; rw [stdH_mulVec_of_mem w n y hyU, hψh']

  let φ : B.A → B.A := fun a => ψ.symm (ψ₃ a)
  have hφψ : ∀ a, ψ (φ a) = ψ₃ a := fun a => ψ.apply_symm_apply _
  have hφs : ∀ (c : K.E) (a : B.A), φ (c • a) = c • φ a := by
    intro c a; apply ψ.injective; rw [hψs, hφψ, hφψ, h3s]
  have hφu : ∀ a, φ (u * a) = u * φ a := by
    intro a; apply ψ.injective; rw [hψu, hφψ, hφψ, h3u]
  have hφadd : ∀ a b, φ (a + b) = φ a + φ b := by
    intro a b; apply ψ.injective; rw [map_add, hφψ, hφψ, hφψ]; simp [ψ₃, Matrix.mulVec_add]

  have hφmul : ∀ a b, φ (a * b) = a * φ b := by
    intro a
    have ha : a ∈ Algebra.adjoin K.E {u} := by rw [hadj]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff] at hz; subst hz; exact hφu
    | algebraMap r =>
      intro b; rw [← Algebra.smul_def, ← Algebra.smul_def, hφs]
    | add a₁ a₂ _ _ h₁ h₂ =>
      intro b; rw [add_mul, hφadd, h₁, h₂, add_mul]
    | mul a₁ a₂ _ _ h₁ h₂ =>
      intro b; rw [mul_assoc, h₁, h₂, mul_assoc]
  have hφ : ∀ a, φ a = a * φ 1 := fun a => by rw [← hφmul, mul_one]

  obtain ⟨a₀, ha₀⟩ : ∃ a₀, φ a₀ = 1 := by
    refine ⟨ψ'.symm ((y⁻¹ : GLw n w).val *ᵥ ψ 1), ?_⟩
    apply ψ.injective
    rw [hφψ]
    simp only [ψ₃, AddEquiv.apply_symm_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  let c : B.Aˣ := ⟨φ 1, a₀, by rw [mul_comm, ← hφ, ha₀], by rw [← hφ, ha₀]⟩
  refine ⟨c, ?_⟩

  have hh : ∀ a b, B.herm x' a b = B.herm x (φ a) (φ b) := by
    intro a b; apply e.injective; rw [← h3h, ← hψh, hφψ, hφψ]
  have htr : ∀ z : B.A, Algebra.trace K.E B.A ((x * ((c : B.A) * B.σ (c : B.A)) - x') * z) = 0 := by
    intro z
    have := hh z 1
    simp only [GlobalTheory.UnitLemma.InvAlg.herm, map_one, mul_one] at this
    rw [hφ z] at this
    have hc : (c : B.A) = φ 1 := rfl
    rw [hc, sub_mul, map_sub, sub_eq_zero, this]
    congr 1; ring
  haveI : IsReduced B.A := isReduced_of_adjoin_squarefree u hadj _ (hQ.map.squarefree) hroot
  exact (sub_eq_zero.1 (GlobalTheory.RegSS.eq_zero_of_trace_mul_eq_zero _ htr)).symm

end GlobalTheory.KapLat
