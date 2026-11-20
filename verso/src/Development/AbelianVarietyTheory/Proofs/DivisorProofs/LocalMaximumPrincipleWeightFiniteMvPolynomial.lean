import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialEvalBoundOnCircleFamily

namespace GlobalTheory

open Polynomial in
/- English proof (translation)
Establish `h` using `ht.norm_lt_cauchyBound hp.ne_zero`. Establish `hs : ((Finset.range p.natDegree).sup fun k => ‖p.coeff k‖₊) ≤ ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖₊` using `Finset.sup_le fun k hk => Finset.single_le_sum (f := fun k => ‖p.coeff k‖₊) (fun _ _ => zero_le) (Finset.mem_range.2 (by have := Finset.mem_range.1 hk; omega))`. Establish `hb : p.cauchyBound ≤ 1 + ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖₊`. Unfold `Polynomial.cauchyBound`. Rewrite using `[hp.leadingCoeff, nnnorm_one, div_one, add_comm]`.

Use `gcongr`. Establish `h2 : ‖t‖₊ ≤ 1 + ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖₊` using `h.le.trans hb`. Establish `h3` using `NNReal.coe_le_coe.mpr h2`. Simplify `h3` using `[NNReal.coe_sum]`.
-/
private lemma norm_le_one_add_sum_norm_coeff_of_isRoot_monic {p : Polynomial ℂ} (hp : p.Monic) {t : ℂ} (ht : p.IsRoot t) :
    ‖t‖ ≤ 1 + ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖ := by
  have h := ht.norm_lt_cauchyBound hp.ne_zero
  have hs : ((Finset.range p.natDegree).sup fun k => ‖p.coeff k‖₊) ≤
      ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖₊ :=
    Finset.sup_le fun k hk => Finset.single_le_sum (f := fun k => ‖p.coeff k‖₊)
      (fun _ _ => zero_le) (Finset.mem_range.2 (by have := Finset.mem_range.1 hk; omega))
  have hb : p.cauchyBound ≤ 1 + ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖₊ := by
    unfold Polynomial.cauchyBound
    rw [hp.leadingCoeff, nnnorm_one, div_one, add_comm]
    gcongr
  have h2 : ‖t‖₊ ≤ 1 + ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖₊ := h.le.trans hb
  have h3 := NNReal.coe_le_coe.mpr h2
  simpa [NNReal.coe_sum] using h3

open Polynomial in
/- English proof (translation)
Rewrite using `[MvPolynomial.eval_map]`. Use `MvPolynomial.ringHom_ext (f := x.comp (algebraMap (MvPolynomial (Fin d) ℚ) B)) (g := MvPolynomial.eval₂Hom (algebraMap ℚ ℂ) (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i)))) (fun r => by` as an intermediate fact. Establish `h` using `map_ratCast (x.comp ((algebraMap (MvPolynomial (Fin d) ℚ) B).comp MvPolynomial.C)) r`. Rewrite using `[MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, eq_ratCast (algebraMap ℚ ℂ)]`. Conclude with `h) (fun i => by simp)`.

Conclude with `congrArg (fun g => g a) this`.
-/
private lemma ringHom_algebraMap_eq_eval_map {d : ℕ} {B : Type} [CommRing B] [Algebra (MvPolynomial (Fin d) ℚ) B]
    (x : B →+* ℂ) (a : MvPolynomial (Fin d) ℚ) :
    x (algebraMap (MvPolynomial (Fin d) ℚ) B a) =
      MvPolynomial.eval (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i)))
        (MvPolynomial.map (algebraMap ℚ ℂ) a) := by
  rw [MvPolynomial.eval_map]
  have := MvPolynomial.ringHom_ext (f := x.comp (algebraMap (MvPolynomial (Fin d) ℚ) B))
    (g := MvPolynomial.eval₂Hom (algebraMap ℚ ℂ)
      (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))))
    (fun r => by
      have h := map_ratCast (x.comp ((algebraMap (MvPolynomial (Fin d) ℚ) B).comp MvPolynomial.C)) r
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, eq_ratCast (algebraMap ℚ ℂ)]
      exact h) (fun i => by simp)
  exact congrArg (fun g => g a) this

open Polynomial in
/- English proof (translation)
Take `⟨p, hpm, hp⟩` from `Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℚ) b`. Establish `hc : ∀ a : MvPolynomial (Fin d) ℚ, ∃ C : ℝ, ∀ z ∈ T, ‖MvPolynomial.eval z (MvPolynomial.map (algebraMap ℚ ℂ) a)‖ ≤ C`. Introduce `a`. Take `⟨C, hC⟩` from `(hT.image (MvPolynomial.continuous_eval (MvPolynomial.map (algebraMap ℚ ℂ) a))).isBounded.exists_norm_le`. Conclude with `⟨C, fun z hz => hC _ ⟨z, hz, rfl⟩⟩`.

Use `choose C hC using hc`. Use `⟨1 + ∑ k ∈ Finset.range (p.natDegree + 1), C (p.coeff k), fun x hx => ?_⟩` and prove the remaining obligations. Use `set f := x.comp (algebraMap (MvPolynomial (Fin d) ℚ) B)`. Establish `hqm : (p.map f).Monic` using `hpm.map f`. Establish `hroot : (p.map f).IsRoot (x b)`.

Rewrite using `[Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂, hp, map_zero]`. Use `(norm_le_one_add_sum_norm_coeff_of_isRoot_monic hqm hroot).trans ?_` and prove the remaining obligations. Rewrite using `[hpm.natDegree_map]`. Use `gcongr with k hk`. Rewrite using `[Polynomial.coeff_map]`.

Simplify using `only [f, RingHom.comp_apply]`. Rewrite using `[ringHom_algebraMap_eq_eval_map]`. Conclude with `hC _ _ hx`.
-/
private lemma exists_norm_le_of_isCompact_homs_over {d : ℕ} {B : Type} [CommRing B] [Algebra (MvPolynomial (Fin d) ℚ) B]
    [Module.Finite (MvPolynomial (Fin d) ℚ) B] {T : Set (Fin d → ℂ)} (hT : IsCompact T) (b : B) :
    ∃ M : ℝ, ∀ x : B →+* ℂ,
      (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) ∈ T → ‖x b‖ ≤ M := by
  classical
  obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℚ) b
  have hc : ∀ a : MvPolynomial (Fin d) ℚ, ∃ C : ℝ, ∀ z ∈ T,
      ‖MvPolynomial.eval z (MvPolynomial.map (algebraMap ℚ ℂ) a)‖ ≤ C := by
    intro a
    obtain ⟨C, hC⟩ := (hT.image (MvPolynomial.continuous_eval
      (MvPolynomial.map (algebraMap ℚ ℂ) a))).isBounded.exists_norm_le
    exact ⟨C, fun z hz => hC _ ⟨z, hz, rfl⟩⟩
  choose C hC using hc
  refine ⟨1 + ∑ k ∈ Finset.range (p.natDegree + 1), C (p.coeff k), fun x hx => ?_⟩
  set f := x.comp (algebraMap (MvPolynomial (Fin d) ℚ) B)
  have hqm : (p.map f).Monic := hpm.map f
  have hroot : (p.map f).IsRoot (x b) := by
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂,
      hp, map_zero]
  refine (norm_le_one_add_sum_norm_coeff_of_isRoot_monic hqm hroot).trans ?_
  rw [hpm.natDegree_map]
  gcongr with k hk
  rw [Polynomial.coeff_map]
  simp only [f, RingHom.comp_apply]
  rw [ringHom_algebraMap_eq_eval_map]
  exact hC _ _ hx

open Polynomial in
/- English proof (translation)
Use `choose M hM using fun b : B => exists_norm_le_of_isCompact_homs_over hT b`. Use `set S : Set (B → ℂ) := {g | g 1 = 1 ∧ (∀ a c, g (a + c) = g a + g c) ∧ (∀ a c, g (a * c) = g a * g c)} ∩ (fun g : B → ℂ => fun i => g (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) ⁻¹' T with hSdef`. Establish `hS : (fun x : B →+* ℂ => (x : B → ℂ)) '' {x : B →+* ℂ | (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) ∈ T} = S`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨⟨map_one x, map_add x, map_mul x⟩, hx⟩`. Introduce and unpack `⟨⟨h1, hadd, hmul⟩, hT'⟩`. Set `x : B →+* ℂ` to `{ toFun := g, map_one' := h1, map_mul' := hmul, map_add' := hadd, map_zero' := by`. Use `hadd 0 0` as an intermediate fact.

Simplify using `only [add_zero] at this`. Take the linear combination `-this }`. Conclude with `⟨x, hT', rfl⟩`. Rewrite using `[hS]`. Establish `hclosed : IsClosed S`.

Use `IsClosed.inter ?_ (hT.isClosed.preimage (continuous_pi fun i => continuous_apply _))` and prove the remaining obligations. Use `IsClosed.inter (isClosed_eq (continuous_apply 1) continuous_const) (IsClosed.inter ?_ ?_)` and prove the remaining obligations. Use `show IsClosed {g : B → ℂ | ∀ a c, g (a + c) = g a + g c}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun a : B => isClosed_iInter fun c : B => isClosed_eq (f := fun g : B → ℂ => g (a + c)) (g := fun g => g a + g c) (continuous_apply (a + c)) ((continuous_apply a).add (continuous_apply c))`.

Use `show IsClosed {g : B → ℂ | ∀ a c, g (a * c) = g a * g c}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun a : B => isClosed_iInter fun c : B => isClosed_eq (f := fun g : B → ℂ => g (a * c)) (g := fun g => g a * g c) (continuous_apply (a * c)) ((continuous_apply a).mul (continuous_apply c))`. Use `(isCompact_univ_pi fun b => isCompact_closedBall (0 : ℂ) (M b)).of_isClosed_subset hclosed ?_` and prove the remaining obligations. Rewrite using `[← hS]`.

Introduce and unpack `_ ⟨x, hx, rfl⟩ b -`. Simplify using `using hM b x hx`.
-/
private lemma isCompact_image_homs_over_isCompact {d : ℕ} {B : Type} [CommRing B]
    [Algebra (MvPolynomial (Fin d) ℚ) B] [Module.Finite (MvPolynomial (Fin d) ℚ) B]
    {T : Set (Fin d → ℂ)} (hT : IsCompact T) :
    IsCompact ((fun x : B →+* ℂ => (x : B → ℂ)) '' {x : B →+* ℂ |
      (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) ∈ T}) := by
  classical
  choose M hM using fun b : B => exists_norm_le_of_isCompact_homs_over hT b
  set S : Set (B → ℂ) := {g | g 1 = 1 ∧ (∀ a c, g (a + c) = g a + g c) ∧ (∀ a c, g (a * c) = g a * g c)} ∩
    (fun g : B → ℂ => fun i => g (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) ⁻¹' T
    with hSdef
  have hS : (fun x : B →+* ℂ => (x : B → ℂ)) '' {x : B →+* ℂ |
      (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) ∈ T} = S := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨map_one x, map_add x, map_mul x⟩, hx⟩
    · rintro ⟨⟨h1, hadd, hmul⟩, hT'⟩
      let x : B →+* ℂ :=
        { toFun := g, map_one' := h1, map_mul' := hmul, map_add' := hadd,
          map_zero' := by
            have := hadd 0 0
            simp only [add_zero] at this
            linear_combination -this }
      exact ⟨x, hT', rfl⟩
  rw [hS]
  have hclosed : IsClosed S := by
    refine IsClosed.inter ?_ (hT.isClosed.preimage (continuous_pi fun i => continuous_apply _))
    refine IsClosed.inter (isClosed_eq (continuous_apply 1) continuous_const) (IsClosed.inter ?_ ?_)
    · show IsClosed {g : B → ℂ | ∀ a c, g (a + c) = g a + g c}
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun a : B => isClosed_iInter fun c : B =>
        isClosed_eq (f := fun g : B → ℂ => g (a + c)) (g := fun g => g a + g c) (continuous_apply (a + c)) ((continuous_apply a).add (continuous_apply c))
    · show IsClosed {g : B → ℂ | ∀ a c, g (a * c) = g a * g c}
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun a : B => isClosed_iInter fun c : B =>
        isClosed_eq (f := fun g : B → ℂ => g (a * c)) (g := fun g => g a * g c) (continuous_apply (a * c)) ((continuous_apply a).mul (continuous_apply c))
  refine (isCompact_univ_pi fun b => isCompact_closedBall (0 : ℂ) (M b)).of_isClosed_subset hclosed ?_
  rw [← hS]
  rintro _ ⟨x, hx, rfl⟩ b -
  simpa using hM b x hx

open Polynomial in
/- English proof (translation)
Take `⟨gens, hgens⟩` from `Module.Finite.fg_top (R := MvPolynomial (Fin d) ℚ) (M := B)`. Use `set φ : MvPolynomial (Fin d) ℚ →+* ℂ := MvPolynomial.eval₂Hom (algebraMap ℚ ℂ) z`. Establish `hcomp : ∀ x : B →+* ℂ, (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) = z → ∀ a, x (algebraMap (MvPolynomial (Fin d) ℚ) B a) = φ a`. Introduce `x hx a`. Rewrite using `[ringHom_algebraMap_eq_eval_map, hx, MvPolynomial.eval_map]`.

Both sides reduce to the same expression. Use `choose p hpm hp using fun b : B => Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℚ) b`. Establish `hroot : ∀ x : B →+* ℂ, (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) = z → ∀ b, x b ∈ ((p b).map φ).roots.toFinset`. Introduce `x hx b`. Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots ((hpm b).map φ).ne_zero]`.

Establish `h1 : (p b).map φ = (p b).map (x.comp (algebraMap (MvPolynomial (Fin d) ℚ) B))`. Use `congr 1`. Use extensionality with `a`. Conclude with `(hcomp x hx (MvPolynomial.C a)).symm`. Conclude with `(hcomp x hx (MvPolynomial.X _)).symm`.

Rewrite using `[h1, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂, hp b, map_zero]`. Establish `hinj : Set.InjOn (fun x : B →+* ℂ => fun b : gens => x b) {x : B →+* ℂ | (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) = z}`. Introduce `x hx x' hx' hxx`. Establish `hspan : ∀ b ∈ Submodule.span (MvPolynomial (Fin d) ℚ) (gens : Set B), x b = x' b`. Introduce `b hb`.

Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem c hc => exact congrFun hxx ⟨c, hc⟩`. Consider the case `zero => simp`. Consider the case `add a c _ _ ha hc => simp [ha, hc]`. Consider the case `smul a c _ hc => rw [Algebra.smul_def, map_mul, map_mul, hc, hcomp x hx, hcomp x' hx']`.

Use extensionality with `b`. Conclude with `hspan b (hgens ▸ Submodule.mem_top)`. Use `Set.Finite.of_finite_image ?_ hinj` and prove the remaining obligations. Use `(Set.Finite.pi (t := fun b : gens => (((p b).map φ).roots.toFinset : Set ℂ)) fun b => Finset.finite_toSet _).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩ b -`.

Conclude with `hroot x hx b`.
-/
private lemma finite_setOf_homs_over_point {d : ℕ} {B : Type} [CommRing B]
    [Algebra (MvPolynomial (Fin d) ℚ) B] [Module.Finite (MvPolynomial (Fin d) ℚ) B]
    (z : Fin d → ℂ) :
    {x : B →+* ℂ | (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) = z}.Finite := by
  classical
  obtain ⟨gens, hgens⟩ := Module.Finite.fg_top (R := MvPolynomial (Fin d) ℚ) (M := B)
  set φ : MvPolynomial (Fin d) ℚ →+* ℂ := MvPolynomial.eval₂Hom (algebraMap ℚ ℂ) z
  have hcomp : ∀ x : B →+* ℂ,
      (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) = z →
      ∀ a, x (algebraMap (MvPolynomial (Fin d) ℚ) B a) = φ a := by
    intro x hx a
    rw [ringHom_algebraMap_eq_eval_map, hx, MvPolynomial.eval_map]
    rfl
  choose p hpm hp using fun b : B => Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℚ) b
  have hroot : ∀ x : B →+* ℂ,
      (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) = z →
      ∀ b, x b ∈ ((p b).map φ).roots.toFinset := by
    intro x hx b
    rw [Multiset.mem_toFinset, Polynomial.mem_roots ((hpm b).map φ).ne_zero]
    have h1 : (p b).map φ = (p b).map (x.comp (algebraMap (MvPolynomial (Fin d) ℚ) B)) := by
      congr 1
      ext a
      · exact (hcomp x hx (MvPolynomial.C a)).symm
      · exact (hcomp x hx (MvPolynomial.X _)).symm
    rw [h1, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂, hp b, map_zero]
  have hinj : Set.InjOn (fun x : B →+* ℂ => fun b : gens => x b)
      {x : B →+* ℂ | (fun i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i))) = z} := by
    intro x hx x' hx' hxx
    have hspan : ∀ b ∈ Submodule.span (MvPolynomial (Fin d) ℚ) (gens : Set B), x b = x' b := by
      intro b hb
      induction hb using Submodule.span_induction with
      | mem c hc => exact congrFun hxx ⟨c, hc⟩
      | zero => simp
      | add a c _ _ ha hc => simp [ha, hc]
      | smul a c _ hc => rw [Algebra.smul_def, map_mul, map_mul, hc, hcomp x hx, hcomp x' hx']
    ext b
    exact hspan b (hgens ▸ Submodule.mem_top)
  refine Set.Finite.of_finite_image ?_ hinj
  refine (Set.Finite.pi (t := fun b : gens => (((p b).map φ).roots.toFinset : Set ℂ))
    fun b => Finset.finite_toSet _).subset ?_
  rintro _ ⟨x, hx, rfl⟩ b -
  exact hroot x hx b

open Polynomial in
/- English proof (translation)
Establish `h` using `Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℚ) hs (Ideal.mem_span_singleton_self s) (Algebra.IsIntegral.isIntegral s)`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Conclude with `⟨a, ha0, Ideal.mem_span_singleton.mp ha⟩`.
-/
private lemma exists_ne_zero_dvd_algebraMap_of_ne_zero {d : ℕ} {B : Type} [CommRing B] [IsDomain B]
    [Algebra (MvPolynomial (Fin d) ℚ) B] [Module.Finite (MvPolynomial (Fin d) ℚ) B]
    {s : B} (hs : s ≠ 0) :
    ∃ a : MvPolynomial (Fin d) ℚ, a ≠ 0 ∧ s ∣ algebraMap (MvPolynomial (Fin d) ℚ) B a := by
  have h := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℚ) hs
    (Ideal.mem_span_singleton_self s) (Algebra.IsIntegral.isIntegral s)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨a, ha0, Ideal.mem_span_singleton.mp ha⟩

open Polynomial in
/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u, MvPolynomial.eval u P ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hP (MvPolynomial.funext fun u => by simpa using h u)`. Use `set q : Polynomial ℂ := MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (z i) + Polynomial.X * Polynomial.C (u i - z i)) P with hq`.

Establish `hqe : ∀ t : ℂ, q.eval t = MvPolynomial.eval (z + t • (u - z)) P`. Introduce `t`. Rewrite using `[hq, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]`. Rewrite using `[MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]`. Use `congr 1`.

Use extensionality with `a`. Simplify using the standard rewrite rules. Use extensionality with `i`. Simplify using the standard rewrite rules. Establish `hq0 : q ≠ 0`.

Introduce `h0`. Apply `hu` to reduce the goal to its premises. Use `hqe 1` as an intermediate fact. Rewrite `this` using `[h0, Polynomial.eval_zero, one_smul]`. Simplify using `using this.symm`.

Use `set r₁ : ℝ := min 1 (ρ / (‖u - z‖ + 1))`. Establish `hr₁ : 0 < r₁` using `lt_min one_pos (div_pos hρ (by positivity))`. Take `⟨r, hr, hrS⟩` from `(Set.Ioo_infinite hr₁).exists_notMem_finset (q.roots.toFinset.image fun t => ‖t‖)`. Use `⟨r • (u - z), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_smul, Real.norm_of_nonneg hr.1.le]`.

Establish `h1 : r < ρ / (‖u - z‖ + 1)` using `hr.2.trans_le (min_le_right _ _)`. Rewrite `h1` using `[lt_div_iff₀ (by positivity)]`. Use polynomial arithmetic with `[norm_nonneg (u - z), hr.1]`. Establish `hcont : Continuous fun p : (Fin d → ℂ) × ℂ => MvPolynomial.eval (p.1 + p.2 • (r • (u - z))) P` using `(MvPolynomial.continuous_eval P).comp (continuous_fst.add (continuous_snd.smul continuous_const))`. Establish `hK : IsCompact (Metric.sphere (0 : ℂ) 1)` using `isCompact_sphere 0 1`.

Use `hK.eventually_forall_of_forall_eventually (x₀ := z) (P := fun z' w => MvPolynomial.eval (z' + w • (r • (u - z))) P ≠ 0) ?_` as an intermediate fact. Use `filter_upwards [this] with z' hz' w hw`. Conclude with `hz' w (by simpa using hw)`. Introduce `w hw`. Use `hcont.continuousAt.eventually_ne ?_` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[show w • r • (u - z) = (w * (r : ℂ)) • (u - z) by rw [mul_smul, Complex.coe_smul], ← hqe]`. Introduce `h0`. Apply `hrS` to reduce the goal to its premises. Use `Finset.mem_image.2 ⟨w * r, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Multiset.mem_toFinset, Polynomial.mem_roots hq0]`. Conclude with `h0`. Rewrite `hw` using `[mem_sphere_zero_iff_norm]`. Rewrite using `[norm_mul, hw, one_mul, Complex.norm_real, Real.norm_of_nonneg hr.1.le]`.
-/
private lemma exists_small_direction_eval_circle_ne_zero {d : ℕ} {P : MvPolynomial (Fin d) ℂ} (hP : P ≠ 0)
    (z : Fin d → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ v : Fin d → ℂ, ‖v‖ < ρ ∧
      ∀ᶠ z' in nhds z, ∀ w : ℂ, ‖w‖ = 1 → MvPolynomial.eval (z' + w • v) P ≠ 0 := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, MvPolynomial.eval u P ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (MvPolynomial.funext fun u => by simpa using h u)
  set q : Polynomial ℂ := MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (z i) + Polynomial.X * Polynomial.C (u i - z i)) P with hq
  have hqe : ∀ t : ℂ, q.eval t = MvPolynomial.eval (z + t • (u - z)) P := by
    intro t
    rw [hq, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]
    rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
    congr 1
    · ext a
      simp
    · ext i
      simp
  have hq0 : q ≠ 0 := by
    intro h0
    apply hu
    have := hqe 1
    rw [h0, Polynomial.eval_zero, one_smul] at this
    simpa using this.symm
  set r₁ : ℝ := min 1 (ρ / (‖u - z‖ + 1))
  have hr₁ : 0 < r₁ := lt_min one_pos (div_pos hρ (by positivity))
  obtain ⟨r, hr, hrS⟩ := (Set.Ioo_infinite hr₁).exists_notMem_finset
    (q.roots.toFinset.image fun t => ‖t‖)
  refine ⟨r • (u - z), ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg hr.1.le]
    have h1 : r < ρ / (‖u - z‖ + 1) := hr.2.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg (u - z), hr.1]
  · have hcont : Continuous fun p : (Fin d → ℂ) × ℂ =>
        MvPolynomial.eval (p.1 + p.2 • (r • (u - z))) P :=
      (MvPolynomial.continuous_eval P).comp (continuous_fst.add (continuous_snd.smul continuous_const))
    have hK : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere 0 1
    have := hK.eventually_forall_of_forall_eventually (x₀ := z)
      (P := fun z' w => MvPolynomial.eval (z' + w • (r • (u - z))) P ≠ 0) ?_
    · filter_upwards [this] with z' hz' w hw
      exact hz' w (by simpa using hw)
    · intro w hw
      refine hcont.continuousAt.eventually_ne ?_
      simp only
      rw [show w • r • (u - z) = (w * (r : ℂ)) • (u - z) by rw [mul_smul, Complex.coe_smul], ← hqe]
      intro h0
      apply hrS
      refine Finset.mem_image.2 ⟨w * r, ?_, ?_⟩
      · rw [Multiset.mem_toFinset, Polynomial.mem_roots hq0]
        exact h0
      · rw [mem_sphere_zero_iff_norm] at hw
        rw [norm_mul, hw, one_mul, Complex.norm_real, Real.norm_of_nonneg hr.1.le]

open Polynomial in

/- English proof (translation)
Introduce `d B _ _ _ _ hinj`. Use `letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance`. Introduce `ψ hψ s hs x₀ δ hδ`. Use `set π : (B →+* ℂ) → (Fin d → ℂ) := fun x i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i)) with hπ`. Establish `hev : ∀ b : B, Continuous fun x : B →+* ℂ => x b` using `fun b => (continuous_apply b).comp continuous_induced_dom`.

Establish `hπc : Continuous π` using `continuous_pi fun i => hev _`. Establish `hind : Topology.IsInducing (fun x : B →+* ℂ => (x : B → ℂ))` using `Topology.IsInducing.induced _`. Establish `hcpt : ∀ T : Set (Fin d → ℂ), IsCompact T → IsCompact {x : B →+* ℂ | π x ∈ T}` using `fun T hT => hind.isCompact_iff.mpr (isCompact_image_homs_over_isCompact hT)`. Use `set z := π x₀`. Take `⟨k, e, he⟩` from `((finite_setOf_homs_over_point (B := B) z).diff (t := {x₀})).fin_embedding`.

Establish `hsep : ∀ j, ∃ b : B, e j b ≠ x₀ b`. Introduce `j`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hj : e j ∈ Set.range e` using `⟨j, rfl⟩`.

Rewrite `hj` using `[he]`. Conclude with `hj.2 (RingHom.ext h)`. Use `choose b hb using hsep`. Use `set t : Fin k → ℂ := fun j => e j (b j)`. Use `set K₀ := {x : B →+* ℂ | π x ∈ Metric.closedBall z 1}`.

Establish `hK₀ : IsCompact K₀` using `hcpt _ (isCompact_closedBall z 1)`. Take `⟨C, hC⟩` from `hK₀.exists_bound_of_continuousOn hψ.continuousOn`. Use `set Φ : (B →+* ℂ) × (B →+* ℂ) → ℂ := fun p => ∏ j, (p.2 (b j) - t j) * (p.1 (b j) - t j)⁻¹`. Establish `hΦc : ∀ x, ContinuousAt Φ (x₀, x)`. Introduce `x`.

Use `tendsto_finset_prod _ fun j _ => ?_` and prove the remaining obligations. Use `(((hev (b j)).comp continuous_snd).sub continuous_const).continuousAt.mul ?_` and prove the remaining obligations. Use `((((hev (b j)).comp continuous_fst).sub continuous_const).continuousAt).inv₀ ?_` and prove the remaining obligations. Conclude with `sub_ne_zero.mpr (hb j).symm`. Establish `hΦ0 : Φ (x₀, x₀) = 1` using `Finset.prod_eq_one fun j _ => mul_inv_cancel₀ (sub_ne_zero.mpr (hb j).symm)`.

Establish `hΦj : ∀ j, Φ (x₀, e j) = 0` using `fun j => Finset.prod_eq_zero (Finset.mem_univ j) (by simp [t])`. Establish `hnear : ∀ᶠ p in nhds (x₀, x₀), ‖Φ p‖ < Real.exp (δ / 3)`. Use `(hΦc x₀).norm.eventually (gt_mem_nhds ?_)` and prove the remaining obligations. Use `show ‖Φ (x₀, x₀)‖ < _`. Rewrite using `[hΦ0, norm_one]`.

Conclude with `Real.one_lt_exp_iff.mpr (by linarith)`. Establish `hfar : ∀ j, ∀ᶠ p in nhds (x₀, e j), ‖Φ p‖ < Real.exp (ψ x₀ - C)`. Introduce `j`. Use `(hΦc (e j)).norm.eventually (gt_mem_nhds ?_)` and prove the remaining obligations. Use `show ‖Φ (x₀, e j)‖ < _`.

Rewrite using `[hΦj, norm_zero]`. Conclude with `Real.exp_pos _`. Rewrite `hnear` using `[nhds_prod_eq, Filter.eventually_prod_iff]`. Take `⟨pa, hpa, pb, hpb, hnear⟩` from `hnear`. Establish `hfar' : ∀ j, ∃ pa : (B →+* ℂ) → Prop, (∀ᶠ y in nhds x₀, pa y) ∧ ∃ pb : (B →+* ℂ) → Prop, (∀ᶠ x in nhds (e j), pb x) ∧ ∀ {y}, pa y → ∀ {x}, pb x → ‖Φ (y, x)‖ < Real.exp (ψ x₀ - C)`.

Introduce `j`. Establish `h` using `hfar j`. Rewrite `h` using `[nhds_prod_eq, Filter.eventually_prod_iff]`. Conclude with `h`. Use `choose qa hqa qb hqb hfar using hfar'`.

Use `set Q : (B →+* ℂ) → Prop := fun x => (pb x ∧ ψ x < ψ x₀ + δ / 3) ∨ ∃ j, qb j x`. Establish `hQ : ∀ x, π x = z → {x | Q x} ∈ nhds x`. Introduce `x hx`. Distinguish the cases in `h : x = x₀`. Rewrite using `[h] filter_upwards [hpb, hψ.continuousAt.eventually (gt_mem_nhds (by linarith : ψ x₀ < ψ x₀ + δ / 3))] with y h1 h2`.

Conclude with `Or.inl ⟨h1, h2⟩`. Establish `hxr : x ∈ Set.range e` using `by rw [he]; exact ⟨hx, h⟩`. Take `⟨j, rfl⟩` from `hxr`. Use `filter_upwards [hqb j] with y hy`. Conclude with `Or.inr ⟨j, hy⟩`.

Establish `hKc : IsCompact (π '' (K₀ \ interior {x | Q x}))` using `(hK₀.diff isOpen_interior).image hπc`. Establish `hzK : z ∉ π '' (K₀ \ interior {x | Q x})`. Introduce and unpack `⟨x, hx, hxz⟩`. Conclude with `hx.2 (mem_interior_iff_mem_nhds.mpr (hQ x hxz))`. Take `⟨ρ, hρ, hρz⟩` from `Metric.isOpen_iff.mp hKc.isClosed.isOpen_compl z hzK`.

Establish `hcover : ∀ x, dist (π x) z < min ρ 1 → Q x`. Introduce `x hx`. Assume the negation of the conclusion as `hq`. Establish `hxK : x ∈ K₀ \ interior {x | Q x}` using `⟨Metric.mem_closedBall.mpr (hx.le.trans (min_le_right _ _)), fun hi => hq (show x ∈ {x | Q x} from interior_subset hi)⟩`. Conclude with `hρz (Metric.mem_ball.mpr (hx.trans_le (min_le_left _ _))) ⟨x, hxK, rfl⟩`.

Take `⟨a, ha0, hadvd⟩` from `exists_ne_zero_dvd_algebraMap_of_ne_zero (d := d) (B := B) hs`. Use `set P := MvPolynomial.map (algebraMap ℚ ℂ) a`. Establish `hP : P ≠ 0` using `fun h => ha0 (MvPolynomial.map_injective _ (algebraMap ℚ ℂ).injective (by rw [map_zero]; exact h))`. Take `⟨v, hv, hvz⟩` from `exists_small_direction_eval_circle_ne_zero hP z (ρ := min ρ 1 / 2) (by positivity)`. Take `⟨ε, hε, hεz⟩` from `Metric.eventually_nhds_iff.mp hvz`.

Use `set r := min (ε / 2) (min ρ 1 / 4)`. Establish `hr : 0 < r` using `lt_min (by positivity) (by positivity)`. Use `set T := (fun p : (Fin d → ℂ) × ℂ => p.1 + p.2 • v) '' (Metric.closedBall z r ×ˢ Metric.sphere 0 1)`. Establish `hT : IsCompact T` using `((isCompact_closedBall z r).prod (isCompact_sphere 0 1)).image (continuous_fst.add (continuous_snd.smul continuous_const))`. Establish `hKQ : ∀ x, π x ∈ T → Q x ∧ x ∈ K₀`.

Introduce and unpack `x ⟨⟨z', w⟩, ⟨hz', hw⟩, hxe⟩`. Establish `hd : dist (π x) z < min ρ 1`. Rewrite using `[← hxe, dist_eq_norm]`. Simplify using `only at hz' hw ⊢`. Rewrite `hz'` using `[Metric.mem_closedBall, dist_eq_norm]`.

Rewrite `hw` using `[mem_sphere_zero_iff_norm]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hw, one_mul]`. Establish `: r ≤ min ρ 1 / 4` using `min_le_right _ _`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `⟨hcover x hd, Metric.mem_closedBall.mpr (hd.le.trans (min_le_right _ _))⟩`. Establish `hKs : ∀ x : B →+* ℂ, π x ∈ T → x s ≠ 0`. Introduce and unpack `x ⟨⟨z', w⟩, ⟨hz', hw⟩, hxe⟩ hxs`. Establish `h1` using `hεz (lt_of_le_of_lt (Metric.mem_closedBall.mp hz') ((min_le_left _ _).trans_lt (by linarith))) w (by simpa using hw)`. Apply `h1` to reduce the goal to its premises.

Take `⟨c, hc⟩` from `hadvd`. Establish `h2` using `ringHom_algebraMap_eq_eval_map x a`. Rewrite `h2` using `[hc, map_mul, hxs, zero_mul]`. Simplify using `only at hxe`. Rewrite using `[hxe]`.

Conclude with `h2.symm`. Use `⟨{y | dist (π y) z < r ∧ pa y ∧ (∀ j, qa j y) ∧ (∀ j, y (b j) ≠ t j) ∧ ψ x₀ - δ / 3 < ψ y}, {x | π x ∈ T}, ?_, hcpt T hT, fun x hx => hKs x hx, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hπc.continuousAt.eventually (Metric.ball_mem_nhds z hr), hpa, Filter.eventually_all.2 hqa, Filter.eventually_all.2 fun j => (hev (b j)).continuousAt.eventually_ne (hb j).symm, hψ.continuousAt.eventually (lt_mem_nhds (by linarith : ψ x₀ - δ / 3 < ψ x₀))] with y h1 …`. Conclude with `⟨h1, h2, h3, h4, h5⟩`. Introduce and unpack `N f R hK y ⟨hy1, hy2, hy3, hy4, hy5⟩ set c : Fin (k + k) → ℂ := Fin.append t (fun j => (y (b j) - t j)⁻¹) set G : MvPolynomial (Fin (k + k)) B := MvPolynomial.C f * (∏ j, (MvPolynomial.C (b j) - MvPolynomial.X (Fin.castAdd k j)) * MvPolynomial.X (Fin.natAdd k j)) ^ N`.

Establish `hG : ∀ x : B →+* ℂ, MvPolynomial.eval₂ x c G = x f * Φ (y, x) ^ N`. Introduce `x`. Simplify using `only [G, c, Φ, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X, Fin.append_left, Fin.append_right]`. Use `set R' := R * Real.exp (N * (ψ x₀ + 2 * δ / 3))`. Establish `key` using `_root_.GlobalTheory.maxPrinciple_line_eval₂ d B hinj (k + k) G c (π y) v R' ?_ y (fun i => rfl)`.

Rewrite `key` using `[hG]`. Establish `hΦy : Φ (y, y) = 1` using `Finset.prod_eq_one fun j _ => mul_inv_cancel₀ (sub_ne_zero.mpr (hy4 j))`. Rewrite `key` using `[hΦy, one_pow, mul_one]`. Establish `hR : 0 ≤ R`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Use `mul_neg_of_neg_of_pos h (Real.exp_pos (N * (ψ x₀ + 2 * δ / 3)))` as an intermediate fact. Combine the linear relations using `[norm_nonneg (y f)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← Real.exp_add]`.

Use `_ ≤ R * Real.exp (δ * N) := by gcongr`. Establish `hN : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`. Use the polynomial consequences of the given equalities and inequalities. Use `_ = Real.exp (δ * N) * R := mul_comm _ _`. Introduce `x w hw hx`.

Establish `hxT : π x ∈ T` using `⟨(π y, w), ⟨Metric.mem_closedBall.mpr hy1.le, by simpa using hw⟩, by funext i; exact (hx i).symm⟩`. Take `⟨hQx, hxK₀⟩` from `hKQ x hxT`. Establish `hf` using `hK x hxT`. Establish `hR : 0 ≤ R` using `le_trans (by positivity) hf`. Establish `hxf : ‖x f‖ ≤ R * Real.exp (N * ψ x)`.

Establish `h1 : ‖x f‖ = ‖x f‖ * Real.exp (-(N * ψ x)) * Real.exp (N * ψ x)`. Rewrite using `[mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]`. Rewrite using `[h1]`. Conclude with `mul_le_mul_of_nonneg_right hf (Real.exp_pos _).le`. Establish `hN : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`.

Rewrite using `[hG, norm_mul, norm_pow]`. Break down `hQx with ⟨h1, h2⟩ | ⟨j, hj⟩` into its components or cases. Establish `hΦ` using `hnear hy2 h1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]`.

Use `_ ≤ R' := by show _ ≤ R * Real.exp (N * (ψ x₀ + 2 * δ / 3)) gcongr`. Use the polynomial consequences of the given equalities and inequalities. Establish `hΦ` using `hfar j (hy3 j) hj`. Establish `hψC : ψ x ≤ C` using `le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC x hxK₀)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]`. Use `_ ≤ R' := by show _ ≤ R * Real.exp (N * (ψ x₀ + 2 * δ / 3)) gcongr`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem _root_.GlobalTheory.local_maximum_principle_weight_finite_mvPolynomial_algebra :
    ∀ (d : ℕ) (B : Type) [CommRing B] [IsDomain B] [Algebra (MvPolynomial (Fin d) ℚ) B] [Module.Finite (MvPolynomial (Fin d) ℚ) B], Function.Injective (algebraMap (MvPolynomial (Fin d) ℚ) B) → (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by
  intro d B _ _ _ _ hinj
  letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance
  intro ψ hψ s hs x₀ δ hδ
  classical
  set π : (B →+* ℂ) → (Fin d → ℂ) :=
    fun x i => x (algebraMap (MvPolynomial (Fin d) ℚ) B (MvPolynomial.X i)) with hπ
  have hev : ∀ b : B, Continuous fun x : B →+* ℂ => x b :=
    fun b => (continuous_apply b).comp continuous_induced_dom
  have hπc : Continuous π := continuous_pi fun i => hev _
  have hind : Topology.IsInducing (fun x : B →+* ℂ => (x : B → ℂ)) := Topology.IsInducing.induced _
  have hcpt : ∀ T : Set (Fin d → ℂ), IsCompact T → IsCompact {x : B →+* ℂ | π x ∈ T} :=
    fun T hT => hind.isCompact_iff.mpr (isCompact_image_homs_over_isCompact hT)
  set z := π x₀

  obtain ⟨k, e, he⟩ := ((finite_setOf_homs_over_point (B := B) z).diff (t := {x₀})).fin_embedding
  have hsep : ∀ j, ∃ b : B, e j b ≠ x₀ b := by
    intro j
    by_contra h
    push_neg at h
    have hj : e j ∈ Set.range e := ⟨j, rfl⟩
    rw [he] at hj
    exact hj.2 (RingHom.ext h)
  choose b hb using hsep
  set t : Fin k → ℂ := fun j => e j (b j)

  set K₀ := {x : B →+* ℂ | π x ∈ Metric.closedBall z 1}
  have hK₀ : IsCompact K₀ := hcpt _ (isCompact_closedBall z 1)
  obtain ⟨C, hC⟩ := hK₀.exists_bound_of_continuousOn hψ.continuousOn

  set Φ : (B →+* ℂ) × (B →+* ℂ) → ℂ := fun p => ∏ j, (p.2 (b j) - t j) * (p.1 (b j) - t j)⁻¹
  have hΦc : ∀ x, ContinuousAt Φ (x₀, x) := by
    intro x
    refine tendsto_finset_prod _ fun j _ => ?_
    refine (((hev (b j)).comp continuous_snd).sub continuous_const).continuousAt.mul ?_
    refine ((((hev (b j)).comp continuous_fst).sub continuous_const).continuousAt).inv₀ ?_
    exact sub_ne_zero.mpr (hb j).symm
  have hΦ0 : Φ (x₀, x₀) = 1 :=
    Finset.prod_eq_one fun j _ => mul_inv_cancel₀ (sub_ne_zero.mpr (hb j).symm)
  have hΦj : ∀ j, Φ (x₀, e j) = 0 := fun j =>
    Finset.prod_eq_zero (Finset.mem_univ j) (by simp [t])
  have hnear : ∀ᶠ p in nhds (x₀, x₀), ‖Φ p‖ < Real.exp (δ / 3) := by
    refine (hΦc x₀).norm.eventually (gt_mem_nhds ?_)
    show ‖Φ (x₀, x₀)‖ < _
    rw [hΦ0, norm_one]
    exact Real.one_lt_exp_iff.mpr (by linarith)
  have hfar : ∀ j, ∀ᶠ p in nhds (x₀, e j), ‖Φ p‖ < Real.exp (ψ x₀ - C) := by
    intro j
    refine (hΦc (e j)).norm.eventually (gt_mem_nhds ?_)
    show ‖Φ (x₀, e j)‖ < _
    rw [hΦj, norm_zero]
    exact Real.exp_pos _
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at hnear
  obtain ⟨pa, hpa, pb, hpb, hnear⟩ := hnear
  have hfar' : ∀ j, ∃ pa : (B →+* ℂ) → Prop, (∀ᶠ y in nhds x₀, pa y) ∧
      ∃ pb : (B →+* ℂ) → Prop, (∀ᶠ x in nhds (e j), pb x) ∧
        ∀ {y}, pa y → ∀ {x}, pb x → ‖Φ (y, x)‖ < Real.exp (ψ x₀ - C) := by
    intro j
    have h := hfar j
    rw [nhds_prod_eq, Filter.eventually_prod_iff] at h
    exact h
  choose qa hqa qb hqb hfar using hfar'

  set Q : (B →+* ℂ) → Prop := fun x => (pb x ∧ ψ x < ψ x₀ + δ / 3) ∨ ∃ j, qb j x
  have hQ : ∀ x, π x = z → {x | Q x} ∈ nhds x := by
    intro x hx
    by_cases h : x = x₀
    · rw [h]
      filter_upwards [hpb, hψ.continuousAt.eventually (gt_mem_nhds (by linarith : ψ x₀ < ψ x₀ + δ / 3))]
        with y h1 h2
      exact Or.inl ⟨h1, h2⟩
    · have hxr : x ∈ Set.range e := by rw [he]; exact ⟨hx, h⟩
      obtain ⟨j, rfl⟩ := hxr
      filter_upwards [hqb j] with y hy
      exact Or.inr ⟨j, hy⟩
  have hKc : IsCompact (π '' (K₀ \ interior {x | Q x})) :=
    (hK₀.diff isOpen_interior).image hπc
  have hzK : z ∉ π '' (K₀ \ interior {x | Q x}) := by
    rintro ⟨x, hx, hxz⟩
    exact hx.2 (mem_interior_iff_mem_nhds.mpr (hQ x hxz))
  obtain ⟨ρ, hρ, hρz⟩ := Metric.isOpen_iff.mp hKc.isClosed.isOpen_compl z hzK
  have hcover : ∀ x, dist (π x) z < min ρ 1 → Q x := by
    intro x hx
    by_contra hq
    have hxK : x ∈ K₀ \ interior {x | Q x} :=
      ⟨Metric.mem_closedBall.mpr (hx.le.trans (min_le_right _ _)),
        fun hi => hq (show x ∈ {x | Q x} from interior_subset hi)⟩
    exact hρz (Metric.mem_ball.mpr (hx.trans_le (min_le_left _ _))) ⟨x, hxK, rfl⟩

  obtain ⟨a, ha0, hadvd⟩ := exists_ne_zero_dvd_algebraMap_of_ne_zero (d := d) (B := B) hs
  set P := MvPolynomial.map (algebraMap ℚ ℂ) a
  have hP : P ≠ 0 := fun h =>
    ha0 (MvPolynomial.map_injective _ (algebraMap ℚ ℂ).injective (by rw [map_zero]; exact h))
  obtain ⟨v, hv, hvz⟩ := exists_small_direction_eval_circle_ne_zero hP z (ρ := min ρ 1 / 2) (by positivity)
  obtain ⟨ε, hε, hεz⟩ := Metric.eventually_nhds_iff.mp hvz
  set r := min (ε / 2) (min ρ 1 / 4)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  set T := (fun p : (Fin d → ℂ) × ℂ => p.1 + p.2 • v) '' (Metric.closedBall z r ×ˢ Metric.sphere 0 1)
  have hT : IsCompact T := ((isCompact_closedBall z r).prod (isCompact_sphere 0 1)).image
    (continuous_fst.add (continuous_snd.smul continuous_const))
  have hKQ : ∀ x, π x ∈ T → Q x ∧ x ∈ K₀ := by
    rintro x ⟨⟨z', w⟩, ⟨hz', hw⟩, hxe⟩
    have hd : dist (π x) z < min ρ 1 := by
      rw [← hxe, dist_eq_norm]
      simp only at hz' hw ⊢
      rw [Metric.mem_closedBall, dist_eq_norm] at hz'
      rw [mem_sphere_zero_iff_norm] at hw
      calc ‖z' + w • v - z‖ = ‖(z' - z) + w • v‖ := by congr 1; abel
        _ ≤ ‖z' - z‖ + ‖w‖ * ‖v‖ := (norm_add_le _ _).trans (by rw [norm_smul])
        _ < min ρ 1 := by
          rw [hw, one_mul]
          have : r ≤ min ρ 1 / 4 := min_le_right _ _
          linarith
    exact ⟨hcover x hd, Metric.mem_closedBall.mpr (hd.le.trans (min_le_right _ _))⟩
  have hKs : ∀ x : B →+* ℂ, π x ∈ T → x s ≠ 0 := by
    rintro x ⟨⟨z', w⟩, ⟨hz', hw⟩, hxe⟩ hxs
    have h1 := hεz (lt_of_le_of_lt (Metric.mem_closedBall.mp hz')
      ((min_le_left _ _).trans_lt (by linarith))) w (by simpa using hw)
    apply h1
    obtain ⟨c, hc⟩ := hadvd
    have h2 := ringHom_algebraMap_eq_eval_map x a
    rw [hc, map_mul, hxs, zero_mul] at h2
    simp only at hxe
    rw [hxe]
    exact h2.symm
  refine ⟨{y | dist (π y) z < r ∧ pa y ∧ (∀ j, qa j y) ∧ (∀ j, y (b j) ≠ t j) ∧ ψ x₀ - δ / 3 < ψ y},
    {x | π x ∈ T}, ?_, hcpt T hT, fun x hx => hKs x hx, ?_⟩
  · filter_upwards [hπc.continuousAt.eventually (Metric.ball_mem_nhds z hr), hpa,
      Filter.eventually_all.2 hqa,
      Filter.eventually_all.2 fun j => (hev (b j)).continuousAt.eventually_ne (hb j).symm,
      hψ.continuousAt.eventually (lt_mem_nhds (by linarith : ψ x₀ - δ / 3 < ψ x₀))]
      with y h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro N f R hK y ⟨hy1, hy2, hy3, hy4, hy5⟩
    set c : Fin (k + k) → ℂ := Fin.append t (fun j => (y (b j) - t j)⁻¹)
    set G : MvPolynomial (Fin (k + k)) B := MvPolynomial.C f *
      (∏ j, (MvPolynomial.C (b j) - MvPolynomial.X (Fin.castAdd k j)) *
        MvPolynomial.X (Fin.natAdd k j)) ^ N
    have hG : ∀ x : B →+* ℂ, MvPolynomial.eval₂ x c G = x f * Φ (y, x) ^ N := by
      intro x
      simp only [G, c, Φ, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow,
        MvPolynomial.eval₂_prod, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X, Fin.append_left,
        Fin.append_right]
    set R' := R * Real.exp (N * (ψ x₀ + 2 * δ / 3))
    have key := _root_.GlobalTheory.maxPrinciple_line_eval₂ d B hinj (k + k) G c (π y) v R' ?_ y (fun i => rfl)
    · rw [hG] at key
      have hΦy : Φ (y, y) = 1 :=
        Finset.prod_eq_one fun j _ => mul_inv_cancel₀ (sub_ne_zero.mpr (hy4 j))
      rw [hΦy, one_pow, mul_one] at key
      have hR : 0 ≤ R := by
        by_contra h
        push_neg at h
        have := mul_neg_of_neg_of_pos h (Real.exp_pos (N * (ψ x₀ + 2 * δ / 3)))
        linarith [norm_nonneg (y f)]
      calc ‖y f‖ * Real.exp (-(N * ψ y)) ≤ R' * Real.exp (-(N * ψ y)) :=
            mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
        _ = R * Real.exp (N * (ψ x₀ + 2 * δ / 3) + -(N * ψ y)) := by
            rw [mul_assoc, ← Real.exp_add]
        _ ≤ R * Real.exp (δ * N) := by
            gcongr
            have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
            nlinarith
        _ = Real.exp (δ * N) * R := mul_comm _ _
    · intro x w hw hx
      have hxT : π x ∈ T := ⟨(π y, w), ⟨Metric.mem_closedBall.mpr hy1.le, by simpa using hw⟩,
        by funext i; exact (hx i).symm⟩
      obtain ⟨hQx, hxK₀⟩ := hKQ x hxT
      have hf := hK x hxT
      have hR : 0 ≤ R := le_trans (by positivity) hf
      have hxf : ‖x f‖ ≤ R * Real.exp (N * ψ x) := by
        have h1 : ‖x f‖ = ‖x f‖ * Real.exp (-(N * ψ x)) * Real.exp (N * ψ x) := by
          rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
        rw [h1]
        exact mul_le_mul_of_nonneg_right hf (Real.exp_pos _).le
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      rw [hG, norm_mul, norm_pow]
      rcases hQx with ⟨h1, h2⟩ | ⟨j, hj⟩
      · have hΦ := hnear hy2 h1
        calc ‖x f‖ * ‖Φ (y, x)‖ ^ N ≤ R * Real.exp (N * ψ x) * Real.exp (δ / 3) ^ N :=
              mul_le_mul hxf (pow_le_pow_left₀ (norm_nonneg _) hΦ.le N) (by positivity) (by positivity)
          _ = R * Real.exp (N * ψ x + N * (δ / 3)) := by
              rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
          _ ≤ R' := by
              show _ ≤ R * Real.exp (N * (ψ x₀ + 2 * δ / 3))
              gcongr
              nlinarith
      · have hΦ := hfar j (hy3 j) hj
        have hψC : ψ x ≤ C := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC x hxK₀)
        calc ‖x f‖ * ‖Φ (y, x)‖ ^ N ≤ R * Real.exp (N * ψ x) * Real.exp (ψ x₀ - C) ^ N :=
              mul_le_mul hxf (pow_le_pow_left₀ (norm_nonneg _) hΦ.le N) (by positivity) (by positivity)
          _ = R * Real.exp (N * ψ x + N * (ψ x₀ - C)) := by
              rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
          _ ≤ R' := by
              show _ ≤ R * Real.exp (N * (ψ x₀ + 2 * δ / 3))
              gcongr
              nlinarith

end GlobalTheory
