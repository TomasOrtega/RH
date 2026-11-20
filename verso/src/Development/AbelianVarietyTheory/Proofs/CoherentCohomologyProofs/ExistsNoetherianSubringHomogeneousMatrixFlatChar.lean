import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsWitnessesOfFormallySmoothQuotient
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FlatQuotSMulTopCokerOfMatrixWitnesses

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
/- English proof (translation)
Set `p : Fin a → P` to `fun m => ε (Pi.single m 1)`. Establish `hεsum : ∀ y : Fin a → S, ε y = ∑ m, π (y m) • p m`. Introduce `y`. Use `conv_lhs => rw [show y = ∑ m, y m • Pi.single m 1 from by`. Use function extensionality and compare the values at `j`.

Simplify using `[Finset.sum_apply, Pi.single_apply]]`. Simplify using `[map_sum, p]`. Set `F : (Fin a → B) →ₗ[B] P` to `Fintype.linearCombination B p`. Establish `hF : ∀ β, F β = ∑ m, β m • p m` using `fun β => Fintype.linearCombination_apply B p β`. Establish `hFsurj : Function.Surjective F`.

Introduce `x`. Take `⟨y, rfl⟩` from `hε x`. Conclude with `⟨fun m => π (y m), by rw [hF, hεsum]⟩`. Take `⟨s, hs⟩` from `Module.projective_lifting_property F LinearMap.id hFsurj`. Establish `hlift : ∀ β : Fin a → B, ∃ y : Fin a → S, (fun m => π (y m)) = β`.

Introduce `β`. Use `choose y hy using fun m => hπ (β m)`. Conclude with `⟨y, funext hy⟩`. Establish `hcol : ∀ m : Fin a, ∃ w : Fin b → S, (fun j => π ((Φ.mulVec w) j)) = Pi.single m 1 - s (p m)`. Introduce `m`.

Take `⟨y, hy⟩` from `hlift (Pi.single m 1 - s (p m))`. Establish `h0 : ε y = 0`. Rewrite using `[hεsum, ← hF]`. Establish `: (fun m => π (y m)) = Pi.single m 1 - s (p m)` using `hy`. Rewrite using `[show (fun m => π (y m)) = _ from this, map_sub, hF]`.

Establish `hs' : F (s (p m)) = p m`. Use `congr_arg (fun φ => φ (p m)) hs` as an intermediate fact. Simplify using `using this`. Rewrite using `[hs']`. Simplify using `[Pi.single_apply]`.

Take `⟨w, w', hw⟩` from `(hkerε y).1 h0`. Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, hw]`. Use function extensionality and compare the values at `j`. Simplify using `[hu]`.

Use `choose w hw using hcol`. Establish `hs' : ∀ x, F (s x) = x` using `fun x => by`. Use `congr_arg (fun φ => φ x) hs` as an intermediate fact. Simplify using `using this`. Establish `hcolε : ∀ j, ε (fun l => Φ l j) = 0`.

Introduce `j`. Use `(hkerε _).2 ⟨Pi.single j 1, 0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Set `Ψ : Matrix (Fin b) (Fin a) S` to `Matrix.of fun j m => w m j`.

Establish `hD : ∀ l j, (Φ * Ψ * Φ - Φ) l j ∈ Ideal.span (Set.range g)`. Introduce `l j`. Rewrite using `[← hker, RingHom.mem_ker]`. Establish `hcomp : ∀ m, π ((Φ * Ψ) l m) = (Pi.single m 1 - s (p m) : Fin a → B) l`. Introduce `m`.

Use `congr_fun (hw m) l` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, Ψ]`. Establish `hsum : ∑ m, π (Φ m j) • s (p m) = 0`. Establish `h1` using `hεsum (fun l => Φ l j)`. Rewrite `h1` using `[hcolε j]`.

Repeatedly rewrite using `[← LinearMap.map_smul, ← map_sum, ← h1, map_zero]`. Establish `hsuml` using `congr_fun hsum l`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsuml`. Rewrite using `[Matrix.sub_apply, map_sub, Matrix.mul_apply, map_sum]`. Simplify using `only [AlgHom.coe_toRingHom, map_mul, hcomp, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Rewrite using `[show ∑ m, s (p m) l * π (Φ m j) = ∑ m, π (Φ m j) * s (p m) l from Finset.sum_congr rfl fun _ _ => mul_comm _ _, hsuml]`. Expand and normalize the polynomial expressions, which then agree. Use `choose c hc using fun l j => (Submodule.mem_span_range_iff_exists_fun S).1 (hD l j)`. Use `⟨Ψ, fun k => Matrix.of fun l j => c l j k, ?_⟩` and prove the remaining obligations. Use extensionality with `l j`.

Establish `h1` using `hc l j`. Simplify using `only [smul_eq_mul] at h1`. Simplify using `only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[show ∑ k, g k * c l j k = ∑ k, c l j k * g k from Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]`. Simplify using the standard rewrite rules.
-/
private theorem exists_generalized_inverse_mod_ideal {R S B P : Type} [CommRing R] [CommRing S]
    [Algebra R S] [CommRing B] [Algebra R B] [AddCommGroup P] [Module B P] {a b r : ℕ}
    (Φ : Matrix (Fin a) (Fin b) S) (u : S) (g : Fin r → S) (π : S →ₐ[R] B)
    (hker : RingHom.ker (π : S →+* B) = Ideal.span (Set.range g))
    (hπ : Function.Surjective π) (ε : (Fin a → S) →ₛₗ[(π : S →+* B)] P)
    (hproj : Module.Projective B P) (hε : Function.Surjective ε)
    (hkerε : ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + u • w') (hu : π u = 0) :
    ∃ (Ψ : Matrix (Fin b) (Fin a) S) (E : Fin r → Matrix (Fin a) (Fin b) S),
      Φ * Ψ * Φ = Φ + ∑ k, g k • E k := by
  classical
  let p : Fin a → P := fun m => ε (Pi.single m 1)
  have hεsum : ∀ y : Fin a → S, ε y = ∑ m, π (y m) • p m := by
    intro y
    conv_lhs => rw [show y = ∑ m, y m • Pi.single m 1 from by
      funext j; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, p]
  let F : (Fin a → B) →ₗ[B] P := Fintype.linearCombination B p
  have hF : ∀ β, F β = ∑ m, β m • p m := fun β => Fintype.linearCombination_apply B p β
  have hFsurj : Function.Surjective F := by
    intro x
    obtain ⟨y, rfl⟩ := hε x
    exact ⟨fun m => π (y m), by rw [hF, hεsum]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property F LinearMap.id hFsurj
  have hlift : ∀ β : Fin a → B, ∃ y : Fin a → S, (fun m => π (y m)) = β := by
    intro β
    choose y hy using fun m => hπ (β m)
    exact ⟨y, funext hy⟩
  have hcol : ∀ m : Fin a, ∃ w : Fin b → S,
      (fun j => π ((Φ.mulVec w) j)) = Pi.single m 1 - s (p m) := by
    intro m
    obtain ⟨y, hy⟩ := hlift (Pi.single m 1 - s (p m))
    have h0 : ε y = 0 := by
      rw [hεsum, ← hF]
      have : (fun m => π (y m)) = Pi.single m 1 - s (p m) := hy
      rw [show (fun m => π (y m)) = _ from this, map_sub, hF]
      have hs' : F (s (p m)) = p m := by
        have := congr_arg (fun φ => φ (p m)) hs
        simpa using this
      rw [hs']
      simp [Pi.single_apply]
    obtain ⟨w, w', hw⟩ := (hkerε y).1 h0
    refine ⟨w, ?_⟩
    rw [← hy, hw]
    funext j
    simp [hu]
  choose w hw using hcol
  have hs' : ∀ x, F (s x) = x := fun x => by
    have := congr_arg (fun φ => φ x) hs
    simpa using this
  have hcolε : ∀ j, ε (fun l => Φ l j) = 0 := by
    intro j
    refine (hkerε _).2 ⟨Pi.single j 1, 0, ?_⟩
    funext l
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  let Ψ : Matrix (Fin b) (Fin a) S := Matrix.of fun j m => w m j
  have hD : ∀ l j, (Φ * Ψ * Φ - Φ) l j ∈ Ideal.span (Set.range g) := by
    intro l j
    rw [← hker, RingHom.mem_ker]
    have hcomp : ∀ m, π ((Φ * Ψ) l m) = (Pi.single m 1 - s (p m) : Fin a → B) l := by
      intro m
      have := congr_fun (hw m) l
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Ψ] using this
    have hsum : ∑ m, π (Φ m j) • s (p m) = 0 := by
      have h1 := hεsum (fun l => Φ l j)
      rw [hcolε j] at h1
      simp_rw [← LinearMap.map_smul, ← map_sum, ← h1, map_zero]
    have hsuml := congr_fun hsum l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsuml
    rw [Matrix.sub_apply, map_sub, Matrix.mul_apply, map_sum]
    simp only [AlgHom.coe_toRingHom, map_mul, hcomp, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [show ∑ m, s (p m) l * π (Φ m j) = ∑ m, π (Φ m j) * s (p m) l from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, hsuml]
    ring
  choose c hc using fun l j => (Submodule.mem_span_range_iff_exists_fun S).1 (hD l j)
  refine ⟨Ψ, fun k => Matrix.of fun l j => c l j k, ?_⟩
  ext l j
  have h1 := hc l j
  simp only [smul_eq_mul] at h1
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [show ∑ k, g k * c l j k = ∑ k, c l j k * g k from Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
  simp

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
/- English proof (translation)
Take `⟨B, _, _, π, P, _, _, ε, hsm, hproj, hπ, hX, hεs, hkerε⟩` from `H`. Establish `hfg` using `Algebra.FinitePresentation.ker_fG_of_surjective π hπ`. Take `⟨r, g, hg⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hfg`. Establish `hker : RingHom.ker (π : MvPolynomial ι R →+* B) = Ideal.span (Set.range g)` using `hg.symm`. Establish `hu : π (X i - 1) = 0` using `by rw [map_sub, hX, map_one, sub_self]`.

Use `⟨r, g, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : (MvPolynomial ι R ⧸ RingHom.ker (π : MvPolynomial ι R →+* B)) ≃ₐ[R] B` using `Ideal.quotientKerAlgEquivOfSurjective hπ`. Establish `: Algebra.FormallySmooth R (MvPolynomial ι R ⧸ RingHom.ker (π : MvPolynomial ι R →+* B))` using `Algebra.FormallySmooth.of_equiv e.symm`. Rewrite `this` using `[hker]`. Conclude with `this`.

Establish `hmem : (X i - 1 : MvPolynomial ι R) ∈ Ideal.span (Set.range g)`. Rewrite using `[← hker, RingHom.mem_ker]`. Conclude with `hu`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun (MvPolynomial ι R)).1 hmem`. Conclude with `⟨c, by rw [← hc]; simp [smul_eq_mul]⟩`.

Introduce `k`. Establish `hgk : π (g k) = 0`. Establish `: g k ∈ RingHom.ker (π : MvPolynomial ι R →+* B)`. Rewrite using `[hker]`. Conclude with `Ideal.subset_span ⟨k, rfl⟩`.

Conclude with `this`. Establish `hcol : ∀ m : Fin a, ∃ w w', g k • (Pi.single m 1 : Fin a → MvPolynomial ι R) = Φ.mulVec w + (X i - 1 : MvPolynomial ι R) • w'`. Introduce `m`. Use `(hkerε _).1 ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ]`.

Simplify using `[hgk]`. Use `choose w w' hw using hcol`. Use `⟨Matrix.of fun j m => w m j, Matrix.of fun l m => w' m l, ?_⟩` and prove the remaining obligations. Use extensionality with `l m`. Establish `h1` using `congr_fun (hw m) l`.

Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.single_apply] at h1`. Simplify using `only [Matrix.smul_apply, Matrix.one_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[h1]`. Simplify using `[Matrix.mulVec, dotProduct]`. Conclude with `exists_generalized_inverse_mod_ideal Φ (X i - 1) g π hker hπ ε hproj hεs hkerε hu`.
-/
private theorem chart_witnesses_lemma {ι : Type} [Fintype ι] {R : Type} [CommRing R] {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)) (i : ι)
    (H : ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P) (ε : (Fin a → MvPolynomial ι R) →ₛₗ[(π : MvPolynomial ι R →+* B)] P), Algebra.Smooth R B ∧ Module.Projective B P ∧ Function.Surjective π ∧ π (X i) = 1 ∧ Function.Surjective ε ∧ ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + (X i - 1 : MvPolynomial ι R) • w') :
    ∃ (r : ℕ) (g : Fin r → MvPolynomial ι R),
      Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) ∧
      (∃ c : Fin r → MvPolynomial ι R, (X i - 1 : MvPolynomial ι R) = ∑ k, c k * g k) ∧
      (∀ k, ∃ (C : Matrix (Fin b) (Fin a) (MvPolynomial ι R)) (C' : Matrix (Fin a) (Fin a) (MvPolynomial ι R)),
        g k • (1 : Matrix (Fin a) (Fin a) (MvPolynomial ι R)) = Φ * C + (X i - 1 : MvPolynomial ι R) • C') ∧
      (∃ (Ψ : Matrix (Fin b) (Fin a) (MvPolynomial ι R)) (E : Fin r → Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
        Φ * Ψ * Φ = Φ + ∑ k, g k • E k) := by
  classical
  obtain ⟨B, _, _, π, P, _, _, ε, hsm, hproj, hπ, hX, hεs, hkerε⟩ := H
  have hfg := Algebra.FinitePresentation.ker_fG_of_surjective π hπ
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hker : RingHom.ker (π : MvPolynomial ι R →+* B) = Ideal.span (Set.range g) := hg.symm
  have hu : π (X i - 1) = 0 := by rw [map_sub, hX, map_one, sub_self]
  refine ⟨r, g, ?_, ?_, ?_, ?_⟩
  · have e : (MvPolynomial ι R ⧸ RingHom.ker (π : MvPolynomial ι R →+* B)) ≃ₐ[R] B :=
      Ideal.quotientKerAlgEquivOfSurjective hπ
    have : Algebra.FormallySmooth R (MvPolynomial ι R ⧸ RingHom.ker (π : MvPolynomial ι R →+* B)) :=
      Algebra.FormallySmooth.of_equiv e.symm
    rw [hker] at this
    exact this
  · have hmem : (X i - 1 : MvPolynomial ι R) ∈ Ideal.span (Set.range g) := by
      rw [← hker, RingHom.mem_ker]; exact hu
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial ι R)).1 hmem
    exact ⟨c, by rw [← hc]; simp [smul_eq_mul]⟩
  · intro k
    have hgk : π (g k) = 0 := by
      have : g k ∈ RingHom.ker (π : MvPolynomial ι R →+* B) := by
        rw [hker]; exact Ideal.subset_span ⟨k, rfl⟩
      exact this
    have hcol : ∀ m : Fin a, ∃ w w', g k • (Pi.single m 1 : Fin a → MvPolynomial ι R) =
        Φ.mulVec w + (X i - 1 : MvPolynomial ι R) • w' := by
      intro m
      refine (hkerε _).1 ?_
      rw [LinearMap.map_smulₛₗ]
      simp [hgk]
    choose w w' hw using hcol
    refine ⟨Matrix.of fun j m => w m j, Matrix.of fun l m => w' m l, ?_⟩
    ext l m
    have h1 := congr_fun (hw m) l
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.single_apply] at h1
    simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.of_apply, smul_eq_mul]
    rw [h1]
    simp [Matrix.mulVec, dotProduct]
  · exact exists_generalized_inverse_mod_ideal Φ (X i - 1) g π hker hπ ε hproj hεs hkerε hu

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
/- English proof (translation)
Use `set I := Ideal.span (Set.range g) with hI`. Set `f : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I` to `Ideal.Quotient.mkₐ R I`. Establish `hkerf : RingHom.ker f.toRingHom = I` using `Ideal.Quotient.mkₐ_ker R I`. Set `x : ι → MvPolynomial ι R` to `fun i => X i + ∑ k, a i k * g k`. Set `φ : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ RingHom.ker f.toRingHom ^ 2` to `(Ideal.Quotient.mkₐ R _).comp (aeval x)`.

Establish `hgI : ∀ k, g k ∈ I` using `fun k => Ideal.subset_span ⟨k, rfl⟩`. Establish `hφ : ∀ p ∈ I, φ p = 0`. Establish `hle : I ≤ RingHom.ker φ` using `by show Ideal.span (Set.range g) ≤ RingHom.ker φ`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Simplify using `only [SetLike.mem_coe, RingHom.mem_ker]`. Use `show Ideal.Quotient.mk _ (aeval x (g j)) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, hkerf, h j, pow_two]`. Conclude with `Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (hgI k) (hgI l))`. Conclude with `fun p hp => hle hp`.

Set `s` to `Ideal.Quotient.liftₐ I φ hφ`. Use `Algebra.FormallySmooth.of_split f s ?_` and prove the remaining obligations. Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`.

Establish `hs : s (Ideal.Quotient.mkₐ R I (X i)) = Ideal.Quotient.mk _ (x i)` using `by show (Ideal.Quotient.liftₐ I φ hφ) (Ideal.Quotient.mk I (X i)) = _`. Rewrite using `[Ideal.Quotient.liftₐ_apply]`. Use `erw [Ideal.Quotient.lift_mk]`. Use `show (Ideal.Quotient.mkₐ R _) (aeval x (X i)) = _`. Rewrite using `[aeval_X]`.

Both sides reduce to the same expression. Simplify using `only [AlgHom.comp_apply, hs, AlgHom.id_apply]`. Rewrite using `[AlgHom.kerSquareLift_mk]`. Simplify using `[f, x, Ideal.Quotient.eq_zero_iff_mem.2 (hgI _)]`.
-/
private theorem formallySmooth_quotient_of_aeval_shift_mem_sq {ι R : Type} [CommRing R] {r : ℕ}
    (g : Fin r → MvPolynomial ι R) (a : ι → Fin r → MvPolynomial ι R)
    (b : Fin r → Fin r → Fin r → MvPolynomial ι R)
    (h : ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l)) :
    Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) := by
  set I := Ideal.span (Set.range g) with hI
  let f : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I := Ideal.Quotient.mkₐ R I
  have hkerf : RingHom.ker f.toRingHom = I := Ideal.Quotient.mkₐ_ker R I
  let x : ι → MvPolynomial ι R := fun i => X i + ∑ k, a i k * g k
  let φ : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.mkₐ R _).comp (aeval x)
  have hgI : ∀ k, g k ∈ I := fun k => Ideal.subset_span ⟨k, rfl⟩
  have hφ : ∀ p ∈ I, φ p = 0 := by
    have hle : I ≤ RingHom.ker φ := by
      show Ideal.span (Set.range g) ≤ RingHom.ker φ
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      show Ideal.Quotient.mk _ (aeval x (g j)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, hkerf, h j, pow_two]
      exact Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun l _ =>
        Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (hgI k) (hgI l))
    exact fun p hp => hle hp
  let s := Ideal.Quotient.liftₐ I φ hφ
  refine Algebra.FormallySmooth.of_split f s ?_
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have hs : s (Ideal.Quotient.mkₐ R I (X i)) = Ideal.Quotient.mk _ (x i) := by
    show (Ideal.Quotient.liftₐ I φ hφ) (Ideal.Quotient.mk I (X i)) = _
    rw [Ideal.Quotient.liftₐ_apply]
    erw [Ideal.Quotient.lift_mk]
    show (Ideal.Quotient.mkₐ R _) (aeval x (X i)) = _
    rw [aeval_X]
    rfl
  simp only [AlgHom.comp_apply, hs, AlgHom.id_apply]
  rw [AlgHom.kerSquareLift_mk]
  simp [f, x, Ideal.Quotient.eq_zero_iff_mem.2 (hgI _)]

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in

/- English proof (translation)
Introduce `ι _ _ R _ a b d e Φ hΦ H`. Use `choose r g hsm hc hC hΨ using fun i => chart_witnesses_lemma Φ i (H i)`. Use `choose wa wb hwit using fun i => _root_.GlobalTheory.exists_witnesses_of_formallySmooth_quotient ι R (r i) (g i) (hsm i)`. Use `choose c hc' using hc`. Use `choose C C' hCC using hC`.

Use `choose Ψ E hΨE using hΨ`. Set `pols : (Fin a × Fin b) ⊕ (Σ i, Fin (r i)) ⊕ (Σ i, ι × Fin (r i)) ⊕ (Σ i, Fin (r i) × Fin (r i) × Fin (r i)) ⊕ (Σ i, Fin (r i)) ⊕ (Σ i, Fin (r i) × Fin b × Fin a) ⊕ (Σ i, Fin (r i) × Fin a × Fin a) ⊕ (Σ i, Fin b × Fin a) ⊕ (Σ i, Fin (r i) × Fin a × Fin b) → MvPolynomial ι R` to `Sum.elim (fun x => Φ x.1 x.2) (Sum.elim (fun x => g x.1 x.2) (Sum.elim (fun x => wa x.1 x.2.1 x.2.2) (Sum.elim (fun x => wb x.1 x.2.1 x.2.2.1 x.2.2.2) (Sum.elim (fun x => c x.1 x.2) (Sum.elim (fun x => C x.1 x.2.1 x.2.2.1 x.2.2.2) (Sum.elim (fun x => C' x.1 x.2.1 x.2.2.1 x.2.2.2) …`. Set `T : Set R` to `⋃ j, ↑(pols j).coeffs`. Establish `hT : T.Finite` using `Set.finite_iUnion fun j => Finset.finite_toSet _`. Set `R₀` to `Subring.closure T`.

Establish `hnoeth : IsNoetherianRing R₀` using `is_noetherian_subring_closure T hT`. Set `φ : MvPolynomial ι R₀ →+* MvPolynomial ι R` to `MvPolynomial.map R₀.subtype`. Establish `hφinj : Function.Injective φ` using `MvPolynomial.map_injective _ Subtype.val_injective`. Establish `hlift : ∀ j, ∃ p₀, φ p₀ = pols j`. Introduce `j`.

Establish `: pols j ∈ Set.range φ`. Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`. Introduce `x hx`. Conclude with `⟨⟨x, Subring.subset_closure (Set.mem_iUnion.2 ⟨j, hx⟩)⟩, rfl⟩`. Conclude with `this`.

Use `choose L hL using hlift`. Set `Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀)` to `Matrix.of fun l j => L (Sum.inl (l, j))`. Set `g₀ : ∀ i, Fin (r i) → MvPolynomial ι R₀` to `fun i k => L (Sum.inr (Sum.inl ⟨i, k⟩))`. Set `wa₀ : ∀ i, ι → Fin (r i) → MvPolynomial ι R₀` to `fun i v k => L (Sum.inr (Sum.inr (Sum.inl ⟨i, v, k⟩)))`. Set `wb₀ : ∀ i, Fin (r i) → Fin (r i) → Fin (r i) → MvPolynomial ι R₀` to `fun i j k l => L (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, j, k, l⟩))))`.

Set `c₀ : ∀ i, Fin (r i) → MvPolynomial ι R₀` to `fun i k => L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k⟩)))))`. Set `C₀ : ∀ i, Fin (r i) → Matrix (Fin b) (Fin a) (MvPolynomial ι R₀)` to `fun i k => Matrix.of fun j m => L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k, j, m⟩))))))`. Set `C'₀ : ∀ i, Fin (r i) → Matrix (Fin a) (Fin a) (MvPolynomial ι R₀)` to `fun i k => Matrix.of fun l m => L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k, l, m⟩)))))))`. Set `Ψ₀ : ∀ i, Matrix (Fin b) (Fin a) (MvPolynomial ι R₀)` to `fun i => Matrix.of fun j m => L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, j, m⟩))))))))`. Set `E₀ : ∀ i, Fin (r i) → Matrix (Fin a) (Fin b) (MvPolynomial ι R₀)` to `fun i k => Matrix.of fun l j => L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, k, l, j⟩))))))))`.

Establish `hΦ₀ : ∀ l j, φ (Φ₀ l j) = Φ l j` using `fun l j => hL _`. Establish `hg₀ : ∀ i k, φ (g₀ i k) = g i k` using `fun i k => hL _`. Establish `hwa₀ : ∀ i v k, φ (wa₀ i v k) = wa i v k` using `fun i v k => hL _`. Establish `hwb₀ : ∀ i j k l, φ (wb₀ i j k l) = wb i j k l` using `fun i j k l => hL _`. Establish `hc₀ : ∀ i k, φ (c₀ i k) = c i k` using `fun i k => hL _`.

Establish `hC₀ : ∀ i k j m, φ (C₀ i k j m) = C i k j m` using `fun i k j m => hL _`. Establish `hC'₀ : ∀ i k l m, φ (C'₀ i k l m) = C' i k l m` using `fun i k l m => hL _`. Establish `hΨ₀ : ∀ i j m, φ (Ψ₀ i j m) = Ψ i j m` using `fun i j m => hL _`. Establish `hE₀ : ∀ i k l j, φ (E₀ i k l j) = E i k l j` using `fun i k l j => hL _`. Establish `hφX : ∀ v, φ (X v) = X v` using `fun v => MvPolynomial.map_X _ _`.

Use `⟨R₀, Φ₀, hnoeth, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Matrix.ext fun l j => hΦ₀ l j`. Introduce `l j`. Rewrite using `[_root_.GlobalTheory.mem_polyGrading_iff]`. Introduce `α hα`.

Use `(_root_.GlobalTheory.mem_polyGrading_iff.1 (hΦ l j)) α ?_` and prove the remaining obligations. Rewrite using `[← hΦ₀ l j, MvPolynomial.coeff_map]`. Introduce `h0`. Conclude with `hα (Subtype.val_injective (by simpa using h0))`. Introduce `i`.

Establish `hwit₀ : ∀ j, aeval (fun v => X v + ∑ k, wa₀ i v k * g₀ i k) (g₀ i j) = ∑ k, ∑ l, wb₀ i j k l * (g₀ i k * g₀ i l)`. Introduce `j`. Apply `hφinj` to reduce the goal to its premises. Rewrite using `[aeval_eq_bind₁, MvPolynomial.map_bind₁]`. Simplify using `only [φ] at hg₀ hwa₀ hwb₀ hφX ⊢`.

Simplify using `only [map_add, map_sum, map_mul, hg₀, hwa₀, hwb₀, hφX]`. Rewrite using `[← aeval_eq_bind₁]`. Conclude with `hwit i j`. Use `haveI : Algebra.FormallySmooth R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) := formallySmooth_quotient_of_aeval_shift_mem_sq (g₀ i) (wa₀ i) (wb₀ i) hwit₀`. Use `haveI : Algebra.FinitePresentation R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) := Algebra.FinitePresentation.of_finiteType.1 inferInstance`.

Use `haveI : Algebra.Smooth R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) := ⟨inferInstance, inferInstance⟩`. Use `_root_.GlobalTheory.flat_quotSMulTop_coker_of_matrix_witnesses R₀ (MvPolynomial ι R₀) (r i) a b (g₀ i) (X i - 1) Φ₀ inferInstance ⟨c₀ i, ?_⟩ (fun k => ⟨C₀ i k, C'₀ i k, ?_⟩) ⟨Ψ₀ i, E₀ i, ?_⟩` and prove the remaining obligations. Apply `hφinj` to reduce the goal to its premises. Simplify using `only [map_sub, map_one, map_sum, map_mul, hc₀, hg₀, hφX]`. Conclude with `hc' i`.

Use `Matrix.ext fun l m => ?_` and prove the remaining obligations. Apply `hφinj` to reduce the goal to its premises. Establish `h1` using `congr_fun (congr_fun (hCC i k) l) m`. Simplify using `only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, smul_eq_mul] at h1 ⊢`. Simplify using `only [map_add, map_mul, map_sum, map_sub, map_one, hg₀, hφX, hΦ₀, hC₀, hC'₀, apply_ite φ, map_zero, map_one]`.

Simplify `h1` using `[Φ₀, C₀, C'₀]`. Use `Matrix.ext fun l j => ?_` and prove the remaining obligations. Apply `hφinj` to reduce the goal to its premises. Establish `h1` using `congr_fun (congr_fun (hΨE i) l) j`. Simplify using `only [Matrix.add_apply, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h1 ⊢`.

Simplify using `only [map_add, map_mul, map_sum, hΦ₀, hΨ₀, hE₀, hg₀]`. Conclude with `h1`.
-/
theorem _root_.GlobalTheory.exists_noetherian_subring_homogeneous_matrix_flat_charts :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)), (∀ l j, Φ l j ∈ _root_.GlobalTheory.polyGrading ι R (e j - d l)) → (∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P) (ε : (Fin a → MvPolynomial ι R) →ₛₗ[(π : MvPolynomial ι R →+* B)] P), Algebra.Smooth R B ∧ Module.Projective B P ∧ Function.Surjective π ∧ π (X i) = 1 ∧ Function.Surjective ε ∧ ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + (X i - 1 : MvPolynomial ι R) • w') → ∃ (R₀ : Subring R) (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀)), IsNoetherianRing R₀ ∧ Φ₀.map (MvPolynomial.map R₀.subtype) = Φ ∧ (∀ l j, Φ₀ l j ∈ _root_.GlobalTheory.polyGrading ι R₀ (e j - d l)) ∧ ∀ i : ι, Module.Flat R₀ (QuotSMulTop (X i - 1 : MvPolynomial ι R₀) ((Fin a → MvPolynomial ι R₀) ⧸ LinearMap.range Φ₀.mulVecLin)) := by
  intro ι _ _ R _ a b d e Φ hΦ H
  classical
  choose r g hsm hc hC hΨ using fun i => chart_witnesses_lemma Φ i (H i)
  choose wa wb hwit using fun i => _root_.GlobalTheory.exists_witnesses_of_formallySmooth_quotient ι R (r i) (g i) (hsm i)
  choose c hc' using hc
  choose C C' hCC using hC
  choose Ψ E hΨE using hΨ
  let pols : (Fin a × Fin b) ⊕ (Σ i, Fin (r i)) ⊕ (Σ i, ι × Fin (r i)) ⊕
      (Σ i, Fin (r i) × Fin (r i) × Fin (r i)) ⊕ (Σ i, Fin (r i)) ⊕ (Σ i, Fin (r i) × Fin b × Fin a) ⊕
      (Σ i, Fin (r i) × Fin a × Fin a) ⊕ (Σ i, Fin b × Fin a) ⊕ (Σ i, Fin (r i) × Fin a × Fin b) →
      MvPolynomial ι R :=
    Sum.elim (fun x => Φ x.1 x.2) (Sum.elim (fun x => g x.1 x.2) (Sum.elim (fun x => wa x.1 x.2.1 x.2.2)
      (Sum.elim (fun x => wb x.1 x.2.1 x.2.2.1 x.2.2.2) (Sum.elim (fun x => c x.1 x.2)
      (Sum.elim (fun x => C x.1 x.2.1 x.2.2.1 x.2.2.2) (Sum.elim (fun x => C' x.1 x.2.1 x.2.2.1 x.2.2.2)
      (Sum.elim (fun x => Ψ x.1 x.2.1 x.2.2) (fun x => E x.1 x.2.1 x.2.2.1 x.2.2.2))))))))
  let T : Set R := ⋃ j, ↑(pols j).coeffs
  have hT : T.Finite := Set.finite_iUnion fun j => Finset.finite_toSet _
  let R₀ := Subring.closure T
  have hnoeth : IsNoetherianRing R₀ := is_noetherian_subring_closure T hT
  let φ : MvPolynomial ι R₀ →+* MvPolynomial ι R := MvPolynomial.map R₀.subtype
  have hφinj : Function.Injective φ := MvPolynomial.map_injective _ Subtype.val_injective
  have hlift : ∀ j, ∃ p₀, φ p₀ = pols j := by
    intro j
    have : pols j ∈ Set.range φ := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro x hx
      exact ⟨⟨x, Subring.subset_closure (Set.mem_iUnion.2 ⟨j, hx⟩)⟩, rfl⟩
    exact this
  choose L hL using hlift
  let Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀) := Matrix.of fun l j => L (Sum.inl (l, j))
  let g₀ : ∀ i, Fin (r i) → MvPolynomial ι R₀ := fun i k => L (Sum.inr (Sum.inl ⟨i, k⟩))
  let wa₀ : ∀ i, ι → Fin (r i) → MvPolynomial ι R₀ := fun i v k =>
    L (Sum.inr (Sum.inr (Sum.inl ⟨i, v, k⟩)))
  let wb₀ : ∀ i, Fin (r i) → Fin (r i) → Fin (r i) → MvPolynomial ι R₀ := fun i j k l =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, j, k, l⟩))))
  let c₀ : ∀ i, Fin (r i) → MvPolynomial ι R₀ := fun i k =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k⟩)))))
  let C₀ : ∀ i, Fin (r i) → Matrix (Fin b) (Fin a) (MvPolynomial ι R₀) := fun i k => Matrix.of fun j m =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k, j, m⟩))))))
  let C'₀ : ∀ i, Fin (r i) → Matrix (Fin a) (Fin a) (MvPolynomial ι R₀) := fun i k => Matrix.of fun l m =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k, l, m⟩)))))))
  let Ψ₀ : ∀ i, Matrix (Fin b) (Fin a) (MvPolynomial ι R₀) := fun i => Matrix.of fun j m =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, j, m⟩))))))))
  let E₀ : ∀ i, Fin (r i) → Matrix (Fin a) (Fin b) (MvPolynomial ι R₀) := fun i k => Matrix.of fun l j =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, k, l, j⟩))))))))
  have hΦ₀ : ∀ l j, φ (Φ₀ l j) = Φ l j := fun l j => hL _
  have hg₀ : ∀ i k, φ (g₀ i k) = g i k := fun i k => hL _
  have hwa₀ : ∀ i v k, φ (wa₀ i v k) = wa i v k := fun i v k => hL _
  have hwb₀ : ∀ i j k l, φ (wb₀ i j k l) = wb i j k l := fun i j k l => hL _
  have hc₀ : ∀ i k, φ (c₀ i k) = c i k := fun i k => hL _
  have hC₀ : ∀ i k j m, φ (C₀ i k j m) = C i k j m := fun i k j m => hL _
  have hC'₀ : ∀ i k l m, φ (C'₀ i k l m) = C' i k l m := fun i k l m => hL _
  have hΨ₀ : ∀ i j m, φ (Ψ₀ i j m) = Ψ i j m := fun i j m => hL _
  have hE₀ : ∀ i k l j, φ (E₀ i k l j) = E i k l j := fun i k l j => hL _
  have hφX : ∀ v, φ (X v) = X v := fun v => MvPolynomial.map_X _ _
  refine ⟨R₀, Φ₀, hnoeth, ?_, ?_, ?_⟩
  · exact Matrix.ext fun l j => hΦ₀ l j
  · intro l j
    rw [_root_.GlobalTheory.mem_polyGrading_iff]
    intro α hα
    refine (_root_.GlobalTheory.mem_polyGrading_iff.1 (hΦ l j)) α ?_
    rw [← hΦ₀ l j, MvPolynomial.coeff_map]
    intro h0
    exact hα (Subtype.val_injective (by simpa using h0))
  · intro i
    have hwit₀ : ∀ j, aeval (fun v => X v + ∑ k, wa₀ i v k * g₀ i k) (g₀ i j) =
        ∑ k, ∑ l, wb₀ i j k l * (g₀ i k * g₀ i l) := by
      intro j
      apply hφinj
      rw [aeval_eq_bind₁, MvPolynomial.map_bind₁]
      simp only [φ] at hg₀ hwa₀ hwb₀ hφX ⊢
      simp only [map_add, map_sum, map_mul, hg₀, hwa₀, hwb₀, hφX]
      rw [← aeval_eq_bind₁]
      exact hwit i j
    haveI : Algebra.FormallySmooth R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) :=
      formallySmooth_quotient_of_aeval_shift_mem_sq (g₀ i) (wa₀ i) (wb₀ i) hwit₀
    haveI : Algebra.FinitePresentation R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) :=
      Algebra.FinitePresentation.of_finiteType.1 inferInstance
    haveI : Algebra.Smooth R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) :=
      ⟨inferInstance, inferInstance⟩
    refine _root_.GlobalTheory.flat_quotSMulTop_coker_of_matrix_witnesses R₀ (MvPolynomial ι R₀) (r i) a b (g₀ i)
      (X i - 1) Φ₀ inferInstance ⟨c₀ i, ?_⟩ (fun k => ⟨C₀ i k, C'₀ i k, ?_⟩) ⟨Ψ₀ i, E₀ i, ?_⟩
    · apply hφinj
      simp only [map_sub, map_one, map_sum, map_mul, hc₀, hg₀, hφX]
      exact hc' i
    · refine Matrix.ext fun l m => ?_
      apply hφinj
      have h1 := congr_fun (congr_fun (hCC i k) l) m
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply,
        smul_eq_mul] at h1 ⊢
      simp only [map_add, map_mul, map_sum, map_sub, map_one, hg₀, hφX, hΦ₀, hC₀, hC'₀,
        apply_ite φ, map_zero, map_one]
      simpa [Φ₀, C₀, C'₀] using h1
    · refine Matrix.ext fun l j => ?_
      apply hφinj
      have h1 := congr_fun (congr_fun (hΨE i) l) j
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul] at h1 ⊢
      simp only [map_add, map_mul, map_sum, hΦ₀, hΨ₀, hE₀, hg₀]
      exact h1

end GlobalTheory
