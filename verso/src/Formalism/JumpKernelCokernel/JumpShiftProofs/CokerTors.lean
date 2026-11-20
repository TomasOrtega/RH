import Formalism.JumpKernelCokernel.Statement
import Formalism.JumpKernelCokernel.JumpShiftProofs.DetLen

open Polynomial Module

namespace Formalism.KernelCokernelLengths.CokernelTorsionLemmas

/- English proof (translation)
Take `⟨g, hg⟩` from `Module.projective_lifting_property S.mkQ LinearMap.id (Submodule.mkQ_surjective S)`. Establish `hg' : ∀ x, S.mkQ (g x) = x` using `fun x => LinearMap.congr_fun hg x`. Set `pr : M →ₗ[R] M` to `LinearMap.id - g ∘ₗ S.mkQ`. Establish `hmem : ∀ m, pr m ∈ S`. Introduce `m`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Simplify using `only [pr, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]`. Rewrite using `[Submodule.Quotient.mk_sub]`. Use `hg' (S.mkQ m)` as an intermediate fact. Simplify using `only [Submodule.mkQ_apply] at this ⊢`.

Rewrite using `[this, sub_self]`. Set `F : M →ₗ[R] S × (M ⧸ S)` to `LinearMap.prod (pr.codRestrict S hmem) S.mkQ`. Set `G : S × (M ⧸ S) →ₗ[R] M` to `S.subtype.coprod g`. Establish `h1 : F ∘ₗ G = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce and unpack `⟨s, c⟩`. Establish `hs : S.mkQ (s : M) = 0` using `by simp`. Establish `hs' : (Submodule.Quotient.mk (s : M) : M ⧸ S) = 0` using `hs`. Establish `hg'' : (Submodule.Quotient.mk (g c) : M ⧸ S) = c` using `hg' c`. Apply `Prod.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[F, G, pr, hg', hs]`. Simplify using `[F, G, pr, hs', hg'']`. Establish `h2 : G ∘ₗ F = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `m`. Simplify using `[F, G, pr]`. Set `e : M ≃ₗ[R] S × (M ⧸ S)` to `LinearEquiv.ofLinearMap (f := F) (g := G) h1 h2`. Set `dS` to `d.restrict (p := S) (q := S) (fun x _ => hd x)`. Set `bS` to `Module.Free.chooseBasis R S`.

Set `bQ` to `Module.Free.chooseBasis R (M ⧸ S)`. Set `b` to `bS.prod bQ`. Establish `hconj : ∀ x, e.conj d x = (⟨d (G x), hd _⟩, 0)`. Introduce `x`. Rewrite using `[LinearEquiv.conj_apply]`.

Establish `hq : S.mkQ (d (G x)) = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hd _`. Apply `Prod.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[e, F, pr, hq]`. Simplify using `[e, F, pr, hq]`. Establish `hM : LinearMap.toMatrix b b (e.conj d) = Matrix.fromBlocks (LinearMap.toMatrix bS bS dS) (LinearMap.toMatrix b b (e.conj d)).toBlocks₁₂ 0 0` using `by conv_lhs => rw [← Matrix.fromBlocks_toBlocks (LinearMap.toMatrix b b (e.conj d))]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `only [Matrix.toBlocks₁₁, Matrix.of_apply, LinearMap.toMatrix_apply, b, Module.Basis.prod_apply, Sum.elim_inl, hconj, Module.Basis.prod_repr_inl]`. Use `congr 2`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[G, dS]`. Use extensionality with `i j`.

Simplify using `[Matrix.toBlocks₂₁, LinearMap.toMatrix_apply, b, hconj]`. Use extensionality with `i j`. Simplify using `[Matrix.toBlocks₂₂, LinearMap.toMatrix_apply, b, hconj]`. Rewrite using `[← e.charpoly_conj d, ← LinearMap.charpoly_toMatrix (e.conj d) b, hM, Matrix.charpoly_fromBlocks_zero₂₁, LinearMap.charpoly_toMatrix, Matrix.charpoly_zero, Module.finrank_eq_card_chooseBasisIndex]`.
-/
theorem charpoly_of_range_le {R : Type} [CommRing R] [IsDomain R] {M : Type} [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M]
    (S : Submodule R M) [Module.Free R S] [Module.Finite R S] [Module.Free R (M ⧸ S)]
    [Module.Finite R (M ⧸ S)] (d : Module.End R M) (hd : ∀ m, d m ∈ S) :
    d.charpoly = (d.restrict (p := S) (q := S) (fun x _ => hd x)).charpoly *
      X ^ finrank R (M ⧸ S) := by
  classical
  obtain ⟨g, hg⟩ := Module.projective_lifting_property S.mkQ LinearMap.id
    (Submodule.mkQ_surjective S)
  have hg' : ∀ x, S.mkQ (g x) = x := fun x => LinearMap.congr_fun hg x
  let pr : M →ₗ[R] M := LinearMap.id - g ∘ₗ S.mkQ
  have hmem : ∀ m, pr m ∈ S := by
    intro m
    rw [← Submodule.Quotient.mk_eq_zero]
    simp only [pr, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [Submodule.Quotient.mk_sub]
    have := hg' (S.mkQ m)
    simp only [Submodule.mkQ_apply] at this ⊢
    rw [this, sub_self]
  let F : M →ₗ[R] S × (M ⧸ S) :=
    LinearMap.prod (pr.codRestrict S hmem) S.mkQ
  let G : S × (M ⧸ S) →ₗ[R] M := S.subtype.coprod g
  have h1 : F ∘ₗ G = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨s, c⟩
    have hs : S.mkQ (s : M) = 0 := by simp
    have hs' : (Submodule.Quotient.mk (s : M) : M ⧸ S) = 0 := hs
    have hg'' : (Submodule.Quotient.mk (g c) : M ⧸ S) = c := hg' c
    apply Prod.ext
    · apply Subtype.ext
      simp [F, G, pr, hg', hs]
    · simp [F, G, pr, hs', hg'']
  have h2 : G ∘ₗ F = LinearMap.id := by
    apply LinearMap.ext
    intro m
    simp [F, G, pr]
  let e : M ≃ₗ[R] S × (M ⧸ S) := LinearEquiv.ofLinearMap (f := F) (g := G) h1 h2
  let dS := d.restrict (p := S) (q := S) (fun x _ => hd x)
  let bS := Module.Free.chooseBasis R S
  let bQ := Module.Free.chooseBasis R (M ⧸ S)
  let b := bS.prod bQ
  have hconj : ∀ x, e.conj d x = (⟨d (G x), hd _⟩, 0) := by
    intro x
    rw [LinearEquiv.conj_apply]
    have hq : S.mkQ (d (G x)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hd _
    apply Prod.ext
    · apply Subtype.ext
      simp [e, F, pr, hq]
    · simp [e, F, pr, hq]
  have hM : LinearMap.toMatrix b b (e.conj d) =
      Matrix.fromBlocks (LinearMap.toMatrix bS bS dS) (LinearMap.toMatrix b b (e.conj d)).toBlocks₁₂
        0 0 := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (LinearMap.toMatrix b b (e.conj d))]
    congr 1
    · ext i j
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply, LinearMap.toMatrix_apply, b,
        Module.Basis.prod_apply, Sum.elim_inl, hconj, Module.Basis.prod_repr_inl]
      congr 2
      apply Subtype.ext
      simp [G, dS]
    · ext i j
      simp [Matrix.toBlocks₂₁, LinearMap.toMatrix_apply, b, hconj]
    · ext i j
      simp [Matrix.toBlocks₂₂, LinearMap.toMatrix_apply, b, hconj]
  rw [← e.charpoly_conj d, ← LinearMap.charpoly_toMatrix (e.conj d) b, hM,
    Matrix.charpoly_fromBlocks_zero₂₁, LinearMap.charpoly_toMatrix, Matrix.charpoly_zero,
    Module.finrank_eq_card_chooseBasisIndex]

end Formalism.KernelCokernelLengths.CokernelTorsionLemmas

namespace Formalism.KernelCokernelLengths.CokernelTorsionLemmas

/- English proof (translation)
Establish `hP0 : P ≠ 0` using `fun h0 => hP (by simp [h0])`. Establish `hQ0 : Q ≠ 0` using `fun h0 => hQ (by simp [h0])`. Establish `tP : P.natTrailingDegree = 0` using `Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hP)`. Establish `tQ : Q.natTrailingDegree = 0` using `Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hQ)`. Establish `hrk : r = k`.

Establish `h1` using `congrArg Polynomial.natTrailingDegree h`. Rewrite `h1` using `[mul_comm (X ^ k) Q, Polynomial.natTrailingDegree_mul_X_pow hP0, Polynomial.natTrailingDegree_mul_X_pow hQ0, tP, tQ]`. Use linear arithmetic over natural numbers and integers. Substitute `hrk` using the available equality. Rewrite `h` using `[mul_comm (X ^ r) Q]`.

Conclude with `mul_right_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) h`.
-/
theorem eq_of_mul_X_pow {R : Type} [CommRing R] [IsDomain R] (P Q : R[X]) (k r : ℕ)
    (hP : P.coeff 0 ≠ 0) (hQ : Q.coeff 0 ≠ 0) (h : P * X ^ r = X ^ k * Q) : P = Q := by
  have hP0 : P ≠ 0 := fun h0 => hP (by simp [h0])
  have hQ0 : Q ≠ 0 := fun h0 => hQ (by simp [h0])
  have tP : P.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hP)
  have tQ : Q.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hQ)
  have hrk : r = k := by
    have h1 := congrArg Polynomial.natTrailingDegree h
    rw [mul_comm (X ^ k) Q, Polynomial.natTrailingDegree_mul_X_pow hP0,
      Polynomial.natTrailingDegree_mul_X_pow hQ0, tP, tQ] at h1
    omega
  subst hrk
  rw [mul_comm (X ^ r) Q] at h
  exact mul_right_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) h

end Formalism.KernelCokernelLengths.CokernelTorsionLemmas

/- English proof (translation)
Introduce `O _ _ _ M _ _ _ _ d k Q hQ0 hchar hann`. Establish `hQc : Q.coeff 0 ≠ 0` using `by rwa [Polynomial.coeff_zero_eq_eval_zero]`. Establish `hdQ : ∀ m, d (aeval d Q m) = 0`. Introduce `m`. Use `LinearMap.congr_fun hann m` as an intermediate fact.

Simplify `this` using `[map_mul, aeval_X]`. Establish `hQd : ∀ m, aeval d Q (d m) = 0`. Introduce `m`. Establish `h0 : aeval d (Q * X) = 0` using `by rw [mul_comm]; exact hann`. Use `LinearMap.congr_fun h0 m` as an intermediate fact.

Simplify `this` using `[map_mul, aeval_X]`. Establish `hsplit : ∀ m, aeval d Q m = Q.coeff 0 • m + d (aeval d Q.divX m)`. Introduce `m`. Use `conv_lhs => rw [← Polynomial.X_mul_divX_add Q]`. Rewrite using `[map_add, map_mul, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply, add_comm]`.

Establish `hcommR : ∀ m, d (aeval d Q.divX m) = aeval d Q.divX (d m)`. Introduce `m`. Establish `h0 : aeval d (X * Q.divX) = aeval d (Q.divX * X)` using `by rw [mul_comm]`. Use `LinearMap.congr_fun h0 m` as an intermediate fact. Simplify `this` using `[map_mul, aeval_X]`.

Set `S : Submodule O M` to `LinearMap.ker (aeval d Q)`. Establish `hdS : ∀ m, d m ∈ S` using `fun m => hQd m`. Establish `htf : Module.IsTorsionFree O (M ⧸ S)`. Use `Module.IsTorsionFree.of_smul_eq_zero (fun a x hx => ?_)` and prove the remaining obligations. Proceed by induction on `x using Submodule.Quotient.induction_on with`.

Consider the case `H m`. Rewrite `hx` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Distinguish the cases in `ha : a = 0`. Conclude with `Or.inl ha`. Use `right`.

Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Establish `: a • aeval d Q m = 0`. Rewrite using `[← map_smul]`. Conclude with `hx`. Conclude with `(smul_eq_zero.mp this).resolve_left ha`.

Establish `: Module.Free O (M ⧸ S)` using `Module.free_of_finite_type_torsion_free'`. Set `dS` to `d.restrict (p := S) (q := S) (fun x _ => hdS x)`. Establish `hc` using `Formalism.KernelCokernelLengths.CokernelTorsionLemmas.charpoly_of_range_le S d hdS`. Establish `hker : LinearMap.ker dS = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`.

Introduce `s hs`. Establish `hs1 : d (s : M) = 0`. Use `congrArg Subtype.val hs` as an intermediate fact. Simplify `this` using `[dS]`. Establish `hs2 : aeval d Q (s : M) = 0` using `s.2`.

Rewrite `hs2` using `[hsplit, hcommR, hs1, map_zero, add_zero]`. Conclude with `Subtype.ext ((smul_eq_zero.mp hs2).resolve_left hQc)`. Establish `hdet : LinearMap.det dS ≠ 0` using `fun h => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hker`. Establish `hPc : dS.charpoly.coeff 0 ≠ 0`. Introduce `h`.

Apply `hdet` to reduce the goal to its premises. Rewrite using `[LinearMap.det_eq_sign_charpoly_coeff, h, mul_zero]`. Establish `hPQ : dS.charpoly = Q` using `Formalism.KernelCokernelLengths.CokernelTorsionLemmas.eq_of_mul_X_pow _ _ k _ hPc hQc (hc.symm.trans hchar)`. Establish `hspan : Ideal.span {LinearMap.det dS} = Ideal.span {Q.eval 0}`. Rewrite using `[LinearMap.det_eq_sign_charpoly_coeff, hPQ, Polynomial.coeff_zero_eq_eval_zero]`.

Conclude with `Ideal.span_singleton_mul_left_unit ((isUnit_neg_one).pow _) _`. Establish `hlen` using `Formalism.KernelCokernelLengths.determinant_length_formula O S dS hdet`. Rewrite `hlen` using `[hspan]`. Rewrite using `[← hlen]`. Establish `hmemT : ∀ s : S, (LinearMap.range d).mkQ (s : M) ∈ Submodule.torsion O (M ⧸ LinearMap.range d)`.

Introduce `s`. Rewrite using `[Submodule.mem_torsion_iff]`. Use `⟨⟨Q.coeff 0, mem_nonZeroDivisors_of_ne_zero hQc⟩, ?_⟩` and prove the remaining obligations. Use `show Q.coeff 0 • (Submodule.Quotient.mk (s : M) : M ⧸ LinearMap.range d) = 0`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`.

Establish `hs2 : aeval d Q (s : M) = 0` using `s.2`. Rewrite `hs2` using `[hsplit]`. Rewrite using `[eq_neg_of_add_eq_zero_left hs2]`. Conclude with `Submodule.neg_mem _ (LinearMap.mem_range_self d _)`. Set `φ : S →ₗ[O] Submodule.torsion O (M ⧸ LinearMap.range d)` to `((LinearMap.range d).mkQ ∘ₗ S.subtype).codRestrict _ hmemT`.

Establish `hφ : LinearMap.range dS ≤ LinearMap.ker φ`. Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[LinearMap.mem_ker]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (LinearMap.range d).mkQ (d (s : M)) = 0`.

Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `LinearMap.mem_range_self d _`. Use `Module.length_le_of_surjective ((LinearMap.range dS).liftQ φ hφ) ?_` and prove the remaining obligations. Introduce and unpack `⟨x, hx⟩`. Proceed by induction on `x using Submodule.Quotient.induction_on with`.

Consider the case `H m`. Rewrite `hx` using `[Submodule.mem_torsion_iff]`. Take `⟨a, ha⟩` from `hx`. Rewrite `ha` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Take `⟨m', hm'⟩` from `ha`.

Establish `h1 : (a : O) • aeval d Q m = 0`. Rewrite using `[← map_smul]`. Use `show aeval d Q ((a : O) • m) = 0`. Rewrite using `[show (a : O) • m = d m' from hm'.symm]`. Conclude with `hQd m'`.

Establish `hmS : m ∈ S` using `(smul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero a)`. Use `⟨Submodule.Quotient.mk ⟨m, hmS⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.liftQ_apply]`. Both sides reduce to the same expression.
-/
theorem Formalism.KernelCokernelLengths.cokernel_torsion_holds : Formalism.KernelCokernelLengths.CokerTors := by
  intro O _ _ _ M _ _ _ _ d k Q hQ0 hchar hann
  classical
  have hQc : Q.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]

  have hdQ : ∀ m, d (aeval d Q m) = 0 := by
    intro m
    have := LinearMap.congr_fun hann m
    simpa [map_mul, aeval_X] using this
  have hQd : ∀ m, aeval d Q (d m) = 0 := by
    intro m
    have h0 : aeval d (Q * X) = 0 := by rw [mul_comm]; exact hann
    have := LinearMap.congr_fun h0 m
    simpa [map_mul, aeval_X] using this

  have hsplit : ∀ m, aeval d Q m = Q.coeff 0 • m + d (aeval d Q.divX m) := by
    intro m
    conv_lhs => rw [← Polynomial.X_mul_divX_add Q]
    rw [map_add, map_mul, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, add_comm]
  have hcommR : ∀ m, d (aeval d Q.divX m) = aeval d Q.divX (d m) := by
    intro m
    have h0 : aeval d (X * Q.divX) = aeval d (Q.divX * X) := by rw [mul_comm]
    have := LinearMap.congr_fun h0 m
    simpa [map_mul, aeval_X] using this
  let S : Submodule O M := LinearMap.ker (aeval d Q)
  have hdS : ∀ m, d m ∈ S := fun m => hQd m

  have htf : Module.IsTorsionFree O (M ⧸ S) := by
    refine Module.IsTorsionFree.of_smul_eq_zero (fun a x hx => ?_)
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        rw [Submodule.Quotient.mk_eq_zero]
        have : a • aeval d Q m = 0 := by
          rw [← map_smul]; exact hx
        exact (smul_eq_zero.mp this).resolve_left ha
  have : Module.Free O (M ⧸ S) := Module.free_of_finite_type_torsion_free'
  let dS := d.restrict (p := S) (q := S) (fun x _ => hdS x)
  have hc := Formalism.KernelCokernelLengths.CokernelTorsionLemmas.charpoly_of_range_le S d hdS

  have hker : LinearMap.ker dS = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro s hs
    have hs1 : d (s : M) = 0 := by
      have := congrArg Subtype.val hs
      simpa [dS] using this
    have hs2 : aeval d Q (s : M) = 0 := s.2
    rw [hsplit, hcommR, hs1, map_zero, add_zero] at hs2
    exact Subtype.ext ((smul_eq_zero.mp hs2).resolve_left hQc)
  have hdet : LinearMap.det dS ≠ 0 := fun h => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hker
  have hPc : dS.charpoly.coeff 0 ≠ 0 := by
    intro h; apply hdet; rw [LinearMap.det_eq_sign_charpoly_coeff, h, mul_zero]
  have hPQ : dS.charpoly = Q :=
    Formalism.KernelCokernelLengths.CokernelTorsionLemmas.eq_of_mul_X_pow _ _ k _ hPc hQc (hc.symm.trans hchar)
  have hspan : Ideal.span {LinearMap.det dS} = Ideal.span {Q.eval 0} := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, hPQ, Polynomial.coeff_zero_eq_eval_zero]
    exact Ideal.span_singleton_mul_left_unit ((isUnit_neg_one).pow _) _
  have hlen := Formalism.KernelCokernelLengths.determinant_length_formula O S dS hdet
  rw [hspan] at hlen
  rw [← hlen]

  have hmemT : ∀ s : S, (LinearMap.range d).mkQ (s : M) ∈
      Submodule.torsion O (M ⧸ LinearMap.range d) := by
    intro s
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨Q.coeff 0, mem_nonZeroDivisors_of_ne_zero hQc⟩, ?_⟩
    show Q.coeff 0 • (Submodule.Quotient.mk (s : M) : M ⧸ LinearMap.range d) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hs2 : aeval d Q (s : M) = 0 := s.2
    rw [hsplit] at hs2
    rw [eq_neg_of_add_eq_zero_left hs2]
    exact Submodule.neg_mem _ (LinearMap.mem_range_self d _)
  let φ : S →ₗ[O] Submodule.torsion O (M ⧸ LinearMap.range d) :=
    ((LinearMap.range d).mkQ ∘ₗ S.subtype).codRestrict _ hmemT
  have hφ : LinearMap.range dS ≤ LinearMap.ker φ := by
    rintro _ ⟨s, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show (LinearMap.range d).mkQ (d (s : M)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self d _
  refine Module.length_le_of_surjective ((LinearMap.range dS).liftQ φ hφ) ?_
  rintro ⟨x, hx⟩
  induction x using Submodule.Quotient.induction_on with
  | H m =>
    rw [Submodule.mem_torsion_iff] at hx
    obtain ⟨a, ha⟩ := hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at ha
    obtain ⟨m', hm'⟩ := ha
    have h1 : (a : O) • aeval d Q m = 0 := by
      rw [← map_smul]
      show aeval d Q ((a : O) • m) = 0
      rw [show (a : O) • m = d m' from hm'.symm]; exact hQd m'
    have hmS : m ∈ S := (smul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero a)
    refine ⟨Submodule.Quotient.mk ⟨m, hmS⟩, ?_⟩
    rw [Submodule.liftQ_apply]
    rfl
