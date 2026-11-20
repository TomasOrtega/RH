import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistDualWeyl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylLatticeExistsCofactorTwistDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationDualWeightInvolutive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowActEquivariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIsoDetGenMNeZero

noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker Formalism.GradedWeylDivisibility GlobalTheory.ValCmp

namespace GlobalTheory.FunObj

section OnePosition

variable {n : ℕ}

def funExp (l : DomWeight n) : ℕ := (∑ a, l.natW a) - (-l.dual.detShift - l.detShift).toNat

/- English proof (translation)
Simplify using `[DomWeight.detShift, Fin.last]`.
-/
theorem funDetShift_succ {m : ℕ} (l : DomWeight (m + 1)) : l.detShift = l.w (Fin.last m) := by
  simp [DomWeight.detShift, Fin.last]

/- English proof (translation)
Introduce `_ _ h` and use `Int.toNat_le_toNat (sub_le_sub_right (l.anti h) _)`.
-/
theorem funNat_antitone (l : DomWeight n) : Antitone l.natW := fun _ _ h =>
  Int.toNat_le_toNat (sub_le_sub_right (l.anti h) _)

/- English proof (translation)
Simplify using `[DomWeight.natW, funDetShift_succ]`.
-/
theorem funNat_last {m : ℕ} (l : DomWeight (m + 1)) : l.natW (Fin.last m) = 0 := by
  simp [DomWeight.natW, funDetShift_succ]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem funDual_w (l : DomWeight n) (i : Fin n) : l.dual.w i = -l.w i.rev := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h1 : l.w (Fin.last m) ≤ l.w i.rev` using `l.anti (Fin.le_last _)`. Establish `h2 : l.w i.rev ≤ l.w 0` using `l.anti (Fin.zero_le _)`. Simplify using `only [nuDual, DomWeight.natW, funDetShift_succ, funDual_w, Fin.rev_last]`. Use linear arithmetic over natural numbers and integers.
-/
theorem funNat_dual {m : ℕ} (l : DomWeight (m + 1)) : l.dual.natW = nuDual l.natW := by
  funext i
  have h1 : l.w (Fin.last m) ≤ l.w i.rev := l.anti (Fin.le_last _)
  have h2 : l.w i.rev ≤ l.w 0 := l.anti (Fin.zero_le _)
  simp only [nuDual, DomWeight.natW, funDetShift_succ, funDual_w, Fin.rev_last]
  omega

/- English proof (translation)
Simplify using `only [DomWeight.natW, funDetShift_succ, funDual_w, Fin.rev_last]`. Use linear arithmetic over natural numbers and integers.
-/
theorem funExpB_succ {m : ℕ} (l : DomWeight (m + 1)) : (-l.dual.detShift - l.detShift).toNat = l.natW 0 := by
  simp only [DomWeight.natW, funDetShift_succ, funDual_w, Fin.rev_last]
  omega

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => simp [funExp, DomWeight.detShift]`. Consider the case `succ m`. Rewrite using `[funExp, funExpB_succ]`. Conclude with `Nat.sub_add_cancel (Finset.single_le_sum (f := l.natW) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))`.
-/
theorem funExp_add (l : DomWeight n) : funExp l + (-l.dual.detShift - l.detShift).toNat = ∑ a, l.natW a := by
  cases n with
  | zero => simp [funExp, DomWeight.detShift]
  | succ m =>
    rw [funExp, funExpB_succ]
    exact Nat.sub_add_cancel (Finset.single_le_sum (f := l.natW) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))

/- English proof (translation)
Rewrite using `[funExp, funExpB_succ]`.
-/
theorem funExp_succ {m : ℕ} (l : DomWeight (m + 1)) : funExp l = ∑ a, l.natW a - l.natW 0 := by
  rw [funExp, funExpB_succ]

/- English proof (translation)
Consider the cases of `l`. Simplify using `[DomWeight.dual]`.
-/
theorem funDual_dual (l : DomWeight n) : l.dual.dual = l := by
  cases l
  simp [DomWeight.dual]

/- English proof (translation)
Establish `h : cofAct R 0 = AlgHom.id R _` using `MvPolynomial.algHom_ext fun v => v.1.elim0`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem funCof_zero (R : Type) [CommRing R] (f : MP R 0) : cofAct R 0 f = f := by
  have h : cofAct R 0 = AlgHom.id R _ := MvPolynomial.algHom_ext fun v => v.1.elim0
  rw [h]
  rfl

variable (R : Type) [CommRing R] [IsDomain R]

/- English proof (translation)
Take `⟨ε, hε⟩` from `Invol.cofRel_invol R m (nuDual ν) (dualIso_nuDual_antitone hν) (dualIso_nuDual_last ν)`. Establish `h1` using `hε g hg f h`. Rewrite `h1` using `[dualIso_nuDual_nuDual hν hl]`. Establish `h2` using `dualIso_cofRel_zsmul (ε : ℤ) h1`. Rewrite `h2` using `[dualIso_units_smul_smul]`.

Conclude with `⟨ε, h2⟩`.
-/
theorem funCof_rev {m : ℕ} {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) (hl : ν (Fin.last m) = 0) {g f : MP R (m + 1)}
    (hg : g ∈ dualWeyl R (m + 1) (m + 1) (nuDual ν)) (h : CofRel R m (nuDual ν) g f) :
    ∃ ε : ℤˣ, CofRel R m ν ((ε : ℤ) • f) g := by
  obtain ⟨ε, hε⟩ := Invol.cofRel_invol R m (nuDual ν) (dualIso_nuDual_antitone hν) (dualIso_nuDual_last ν)
  have h1 := hε g hg f h
  rw [dualIso_nuDual_nuDual hν hl] at h1
  have h2 := dualIso_cofRel_zsmul (ε : ℤ) h1
  rw [dualIso_units_smul_smul] at h2
  exact ⟨ε, h2⟩

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Introduce `f hf`. Use `⟨f, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show l.dual.natW = l.natW from Subsingleton.elim _ _]` and apply the resulting hypothesis.

Simplify using `[funCof_zero]`. Consider the case `succ m`. Introduce `f hf`. Take `⟨g, hg, h⟩` from `exists_cofRel_dualWeyl R m _ (funNat_antitone l) (funNat_last l) f hf`. Rewrite using `[funNat_dual]`.

Conclude with `⟨g, hg, by rw [funExp_succ]; exact h⟩`.
-/
theorem funPos_nabla (l : DomWeight n) : ∀ f ∈ dualWeyl R n n l.natW, ∃ g ∈ dualWeyl R n n l.dual.natW,
    (genM R n).det ^ funExp l * g = cofAct R n f := by
  cases n with
  | zero =>
    intro f hf
    refine ⟨f, ?_, ?_⟩
    · rwa [show l.dual.natW = l.natW from Subsingleton.elim _ _]
    · simp [funCof_zero]
  | succ m =>
    intro f hf
    obtain ⟨g, hg, h⟩ := exists_cofRel_dualWeyl R m _ (funNat_antitone l) (funNat_last l) f hf
    rw [funNat_dual]
    exact ⟨g, hg, by rw [funExp_succ]; exact h⟩

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Introduce `f hf`. Use `⟨f, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show l.natW = l.dual.natW from Subsingleton.elim _ _]` and apply the resulting hypothesis.

Simplify using `[funCof_zero]`. Consider the case `succ m`. Introduce `g hg`. Rewrite `hg` using `[funNat_dual]`. Establish `hν` using `funNat_antitone l`.

Establish `hl` using `funNat_last l`. Take `⟨f, hf, h⟩` from `exists_cofRel_dualWeyl R m _ (dualIso_nuDual_antitone hν) (dualIso_nuDual_last _) g hg`. Rewrite `hf` using `[dualIso_nuDual_nuDual hν hl]`. Take `⟨ε, h2⟩` from `funCof_rev R hν hl hg h`. Conclude with `⟨(ε : ℤ) • f, zsmul_mem hf _, by rw [funExp_succ]; exact h2⟩`.
-/
theorem funPos_nabla_rev (l : DomWeight n) : ∀ g ∈ dualWeyl R n n l.dual.natW, ∃ f ∈ dualWeyl R n n l.natW,
    (genM R n).det ^ funExp l * g = cofAct R n f := by
  cases n with
  | zero =>
    intro f hf
    refine ⟨f, ?_, ?_⟩
    · rwa [show l.natW = l.dual.natW from Subsingleton.elim _ _]
    · simp [funCof_zero]
  | succ m =>
    intro g hg
    rw [funNat_dual] at hg
    have hν := funNat_antitone l
    have hl := funNat_last l
    obtain ⟨f, hf, h⟩ := exists_cofRel_dualWeyl R m _ (dualIso_nuDual_antitone hν) (dualIso_nuDual_last _) g hg
    rw [dualIso_nuDual_nuDual hν hl] at hf
    obtain ⟨ε, h2⟩ := funCof_rev R hν hl hg h
    exact ⟨(ε : ℤ) • f, zsmul_mem hf _, by rw [funExp_succ]; exact h2⟩

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Introduce `f hf`. Use `⟨f, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show l.dual.natW = l.natW from Subsingleton.elim _ _]` and apply the resulting hypothesis.

Simplify using `[funCof_zero]`. Consider the case `succ m`. Introduce `f hf`. Take `⟨g, hg, h⟩` from `weyl_exists_cofRel R m _ (funNat_antitone l) (funNat_last l) f hf`. Rewrite using `[funNat_dual]`.

Conclude with `⟨g, hg, by rw [funExp_succ]; exact h⟩`.
-/
theorem funPos_weyl (l : DomWeight n) : ∀ f ∈ weyl R n n le_rfl l.natW, ∃ g ∈ weyl R n n le_rfl l.dual.natW,
    (genM R n).det ^ funExp l * g = cofAct R n f := by
  cases n with
  | zero =>
    intro f hf
    refine ⟨f, ?_, ?_⟩
    · rwa [show l.dual.natW = l.natW from Subsingleton.elim _ _]
    · simp [funCof_zero]
  | succ m =>
    intro f hf
    obtain ⟨g, hg, h⟩ := weyl_exists_cofRel R m _ (funNat_antitone l) (funNat_last l) f hf
    rw [funNat_dual]
    exact ⟨g, hg, by rw [funExp_succ]; exact h⟩

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Introduce `f hf`. Use `⟨f, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[show l.natW = l.dual.natW from Subsingleton.elim _ _]` and apply the resulting hypothesis.

Simplify using `[funCof_zero]`. Consider the case `succ m`. Introduce `g hg`. Rewrite `hg` using `[funNat_dual]`. Establish `hν` using `funNat_antitone l`.

Establish `hl` using `funNat_last l`. Take `⟨f, hf, h⟩` from `weyl_exists_cofRel R m _ (dualIso_nuDual_antitone hν) (dualIso_nuDual_last _) g hg`. Rewrite `hf` using `[dualIso_nuDual_nuDual hν hl]`. Take `⟨ε, h2⟩` from `funCof_rev R hν hl (weylLeDual R _ _ _ _ (dualIso_nuDual_antitone hν) hg) h`. Conclude with `⟨(ε : ℤ) • f, zsmul_mem hf _, by rw [funExp_succ]; exact h2⟩`.
-/
theorem funPos_weyl_rev (l : DomWeight n) : ∀ g ∈ weyl R n n le_rfl l.dual.natW, ∃ f ∈ weyl R n n le_rfl l.natW,
    (genM R n).det ^ funExp l * g = cofAct R n f := by
  cases n with
  | zero =>
    intro f hf
    refine ⟨f, ?_, ?_⟩
    · rwa [show l.natW = l.dual.natW from Subsingleton.elim _ _]
    · simp [funCof_zero]
  | succ m =>
    intro g hg
    rw [funNat_dual] at hg
    have hν := funNat_antitone l
    have hl := funNat_last l
    obtain ⟨f, hf, h⟩ := weyl_exists_cofRel R m _ (dualIso_nuDual_antitone hν) (dualIso_nuDual_last _) g hg
    rw [dualIso_nuDual_nuDual hν hl] at hf
    obtain ⟨ε, h2⟩ := funCof_rev R hν hl (weylLeDual R _ _ _ _ (dualIso_nuDual_antitone hν) hg) h
    exact ⟨(ε : ℤ) • f, zsmul_mem hf _, by rw [funExp_succ]; exact h2⟩

end OnePosition

section Map

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {n e : ℕ}

/- English proof (translation)
Establish `h1` using `congrArg (MvPolynomial.map (algebraMap O K)) h`. Rewrite `h1` using `[map_mul, map_pow, RingHom.map_det, dualIso_map_genM, dualIso_map_cofAct]`. Conclude with `h1`.
-/
theorem funMap_rel {f g : MP O n} (h : (genM O n).det ^ e * g = cofAct O n f) :
    (genM K n).det ^ e * MvPolynomial.map (algebraMap O K) g = cofAct K n (MvPolynomial.map (algebraMap O K) f) := by
  have h1 := congrArg (MvPolynomial.map (algebraMap O K)) h
  rw [map_mul, map_pow, RingHom.map_det, dualIso_map_genM, dualIso_map_cofAct] at h1
  exact h1

/- English proof (translation)
Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨g, hg, hfg⟩` from `h f hf`. Conclude with `⟨_, ⟨g, hg, rfl⟩, funMap_rel hfg⟩`.
-/
theorem funMap_fwd (A B : Submodule O (MP O n)) (h : ∀ f ∈ A, ∃ g ∈ B, (genM O n).det ^ e * g = cofAct O n f) :
    ∀ f ∈ A.map (mapAlgHom (Algebra.ofId O K)).toLinearMap, ∃ g ∈ B.map (mapAlgHom (Algebra.ofId O K)).toLinearMap,
      (genM K n).det ^ e * g = cofAct K n f := by
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨g, hg, hfg⟩ := h f hf
  exact ⟨_, ⟨g, hg, rfl⟩, funMap_rel hfg⟩

/- English proof (translation)
Introduce and unpack `_ ⟨g, hg, rfl⟩`. Take `⟨f, hf, hfg⟩` from `h g hg`. Conclude with `⟨_, ⟨f, hf, rfl⟩, funMap_rel hfg⟩`.
-/
theorem funMap_rev (A B : Submodule O (MP O n)) (h : ∀ g ∈ B, ∃ f ∈ A, (genM O n).det ^ e * g = cofAct O n f) :
    ∀ g ∈ B.map (mapAlgHom (Algebra.ofId O K)).toLinearMap, ∃ f ∈ A.map (mapAlgHom (Algebra.ofId O K)).toLinearMap,
      (genM K n).det ^ e * g = cofAct K n f := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨f, hf, hfg⟩ := h g hg
  exact ⟨_, ⟨f, hf, rfl⟩, funMap_rel hfg⟩

end Map

section Tensor

variable {K ι : Type} [Field K] [Fintype ι] {n : ℕ}

def FunRel (a : ι → ℕ) (F G : Pol K ι n) : Prop := (∏ τ, frDet K n τ ^ a τ) * G = dualSubst K ι n F

omit [Fintype ι] in
/- English proof (translation)
Rewrite using `[AlgHom.map_det]`. Unfold `frDet`. Use `congr 1`. Use extensionality with `a s`. Simplify using `[genM, blockEmb]`.
-/
theorem funFrDet_eq (τ : ι) : frDet K n τ = blockEmb K τ (genM K n).det := by
  rw [AlgHom.map_det]
  unfold frDet
  congr 1
  ext a s
  simp [genM, blockEmb]

omit [Fintype ι] in
/- English proof (translation)
Rewrite using `[funFrDet_eq]`. Introduce `h`. Use `dualIso_det_genM_ne_zero K n (rename_injective (fun v => (τ, v)) (fun _ _ h => (Prod.mk.inj h).2) ?_)` and prove the remaining obligations. Rewrite using `[map_zero]`. Conclude with `h`.
-/
theorem funFrDet_ne_zero (τ : ι) : frDet K n τ ≠ 0 := by
  rw [funFrDet_eq]
  intro h
  refine dualIso_det_genM_ne_zero K n (rename_injective (fun v => (τ, v)) (fun _ _ h => (Prod.mk.inj h).2) ?_)
  rw [map_zero]
  exact h

omit [Fintype ι] in
/- English proof (translation)
Establish `h : (dualSubst K ι n).comp (blockEmb K τ) = (blockEmb K τ).comp (cofAct K n)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Establish `hm : (Matrix.of fun a s : Fin n => (X (τ, a, s) : Pol K ι n)) = ((blockEmb K τ : MP K n →ₐ[K] Pol K ι n) : MP K n →+* Pol K ι n).mapMatrix (genM K n)`. Use extensionality with `a s`.

Simplify using `[genM, blockEmb]`. Simplify using `only [AlgHom.comp_apply, dualSubst, cofAct, aeval_X, blockEmb, rename_X]`. Simplify using `only [blockEmb] at hm`. Rewrite using `[hm, ← RingHom.map_adjugate]`. Both sides reduce to the same expression.

Conclude with `DFunLike.congr_fun h f`.
-/
theorem funSubst_blockEmb (τ : ι) (f : MP K n) :
    dualSubst K ι n (blockEmb K τ f) = blockEmb K τ (cofAct K n f) := by
  have h : (dualSubst K ι n).comp (blockEmb K τ) = (blockEmb K τ).comp (cofAct K n) := by
    apply MvPolynomial.algHom_ext
    intro v
    have hm : (Matrix.of fun a s : Fin n => (X (τ, a, s) : Pol K ι n)) =
        ((blockEmb K τ : MP K n →ₐ[K] Pol K ι n) : MP K n →+* Pol K ι n).mapMatrix (genM K n) := by
      ext a s
      simp [genM, blockEmb]
    simp only [AlgHom.comp_apply, dualSubst, cofAct, aeval_X, blockEmb, rename_X]
    simp only [blockEmb] at hm
    rw [hm, ← RingHom.map_adjugate]
    rfl
  exact DFunLike.congr_fun h f

/- English proof (translation)
Unfold `FunRel ten`. Rewrite using `[map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[funSubst_blockEmb, ← h, map_mul, map_pow, funFrDet_eq]`.
-/
theorem funRel_ten {a : ι → ℕ} {f g : ι → MP K n} (h : ∀ τ, (genM K n).det ^ a τ * g τ = cofAct K n (f τ)) :
    FunRel a (ten f) (ten g) := by
  unfold FunRel ten
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [funSubst_blockEmb, ← h, map_mul, map_pow, funFrDet_eq]

/- English proof (translation)
Unfold `FunRel at *`. Rewrite using `[mul_add, map_add, h, h']`.
-/
theorem FunRel.add {a : ι → ℕ} {F F' G G' : Pol K ι n} (h : FunRel a F G) (h' : FunRel a F' G') :
    FunRel a (F + F') (G + G') := by
  unfold FunRel at *
  rw [mul_add, map_add, h, h']

/- English proof (translation)
Unfold `FunRel at *`. Rewrite using `[mul_smul_comm, map_smul, h]`.
-/
theorem FunRel.smul {a : ι → ℕ} {F G : Pol K ι n} (c : K) (h : FunRel a F G) : FunRel a (c • F) (c • G) := by
  unfold FunRel at *
  rw [mul_smul_comm, map_smul, h]

/- English proof (translation)
Rewrite using `[← algebraMap_smul K c F, ← algebraMap_smul K c G]`. Conclude with `h.smul _`.
-/
theorem FunRel.smulOver {O : Type} [CommRing O] [Algebra O K] {a : ι → ℕ} {F G : Pol K ι n} (c : O) (h : FunRel a F G) :
    FunRel a (c • F) (c • G) := by
  rw [← algebraMap_smul K c F, ← algebraMap_smul K c G]
  exact h.smul _

/- English proof (translation)
Simplify using `[FunRel]`.
-/
theorem funRel_zero (a : ι → ℕ) : FunRel (K := K) (n := n) a 0 0 := by
  simp [FunRel]

/- English proof (translation)
The claim follows from `mul_left_cancel₀ (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (funFrDet_ne_zero τ)) (h.trans h'.symm)`.
-/
theorem funRel_unique {a : ι → ℕ} {F G G' : Pol K ι n} (h : FunRel a F G) (h' : FunRel a F G') : G = G' :=
  mul_left_cancel₀ (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (funFrDet_ne_zero τ)) (h.trans h'.symm)

variable {O : Type} [CommRing O] [Algebra O K]

/- English proof (translation)
Introduce `F hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, rfl⟩` from `hx`. Use `choose g hg hg' using fun τ => h τ (f τ) (hf τ)`.

Conclude with `⟨ten g, Submodule.subset_span ⟨g, hg, rfl⟩, funRel_ten hg'⟩`. Consider the case `zero => exact ⟨0, zero_mem _, funRel_zero a⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨G, hG, e⟩` from `hx`. Take `⟨G', hG', e'⟩` from `hy`.

Conclude with `⟨G + G', add_mem hG hG', e.add e'⟩`. Consider the case `smul c x _ hx`. Take `⟨G, hG, e⟩` from `hx`. Conclude with `⟨c • G, Submodule.smul_mem _ c hG, e.smulOver c⟩`.
-/
theorem funRel_exists (M M' : ι → Submodule O (MP K n)) (a : ι → ℕ)
    (h : ∀ τ, ∀ f ∈ M τ, ∃ g ∈ M' τ, (genM K n).det ^ a τ * g = cofAct K n f) :
    ∀ F ∈ tensorLat O K M, ∃ G ∈ tensorLat O K M', FunRel a F G := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    choose g hg hg' using fun τ => h τ (f τ) (hf τ)
    exact ⟨ten g, Submodule.subset_span ⟨g, hg, rfl⟩, funRel_ten hg'⟩
  | zero => exact ⟨0, zero_mem _, funRel_zero a⟩
  | add x y _ _ hx hy =>
    obtain ⟨G, hG, e⟩ := hx
    obtain ⟨G', hG', e'⟩ := hy
    exact ⟨G + G', add_mem hG hG', e.add e'⟩
  | smul c x _ hx =>
    obtain ⟨G, hG, e⟩ := hx
    exact ⟨c • G, Submodule.smul_mem _ c hG, e.smulOver c⟩

/- English proof (translation)
Introduce `G hG`. Proceed by induction on `hG using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, hg, rfl⟩` from `hx`. Use `choose f hf hf' using fun τ => h τ (g τ) (hg τ)`.

Conclude with `⟨ten f, Submodule.subset_span ⟨f, hf, rfl⟩, funRel_ten hf'⟩`. Consider the case `zero => exact ⟨0, zero_mem _, funRel_zero a⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨F, hF, e⟩` from `hx`. Take `⟨F', hF', e'⟩` from `hy`.

Conclude with `⟨F + F', add_mem hF hF', e.add e'⟩`. Consider the case `smul c x _ hx`. Take `⟨F, hF, e⟩` from `hx`. Conclude with `⟨c • F, Submodule.smul_mem _ c hF, e.smulOver c⟩`.
-/
theorem funRel_exists_rev (M M' : ι → Submodule O (MP K n)) (a : ι → ℕ)
    (h : ∀ τ, ∀ g ∈ M' τ, ∃ f ∈ M τ, (genM K n).det ^ a τ * g = cofAct K n f) :
    ∀ G ∈ tensorLat O K M', ∃ F ∈ tensorLat O K M, FunRel a F G := by
  intro G hG
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    choose f hf hf' using fun τ => h τ (g τ) (hg τ)
    exact ⟨ten f, Submodule.subset_span ⟨f, hf, rfl⟩, funRel_ten hf'⟩
  | zero => exact ⟨0, zero_mem _, funRel_zero a⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, e⟩ := hx
    obtain ⟨F', hF', e'⟩ := hy
    exact ⟨F + F', add_mem hF hF', e.add e'⟩
  | smul c x _ hx =>
    obtain ⟨F, hF, e⟩ := hx
    exact ⟨c • F, Submodule.smul_mem _ c hF, e.smulOver c⟩

/- English proof (translation)
Establish `h1 : trAct g (ten f) = ten fun τ => rowAct K ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose (f τ)`. Unfold `ten`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Conclude with `(blockActTensor K K ι n n fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose).1 τ (f τ)`.

Establish `h2 : ∀ (c : ι → K) (x : ι → MP K n), ten (fun τ => c τ • x τ) = (∏ τ, c τ) • ten x`. Introduce `c x`. Unfold `ten`. Simplify using `only [map_smul]`. Rewrite using `[Finset.prod_smul]`.

Rewrite using `[h2, ← h1]`. Both sides reduce to the same expression.
-/
theorem funAct_ten (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (f : ι → MP K n) :
    actP lam g (ten f) = ten fun τ => detPow K n (g τ) (lam τ).detShift •
      rowAct K ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose (f τ) := by
  have h1 : trAct g (ten f) = ten fun τ => rowAct K ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose (f τ) := by
    unfold ten
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact (blockActTensor K K ι n n fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose).1 τ (f τ)
  have h2 : ∀ (c : ι → K) (x : ι → MP K n), ten (fun τ => c τ • x τ) = (∏ τ, c τ) • ten x := by
    intro c x
    unfold ten
    simp only [map_smul]
    rw [Finset.prod_smul]
  rw [h2, ← h1]
  rfl

end Tensor

section ActOne

variable {K : Type} [Field K] {n : ℕ}

/- English proof (translation)
Simplify using `[detPow]`.
-/
theorem funDetPow_eq (h : GL (Fin n) K) (c : ℤ) :
    detPow K n h c = ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ^ c := by
  simp [detPow]

/- English proof (translation)
Simplify using `[inside₂, Matrix.det_transpose, Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`.
-/
theorem funDet_invTr (h : GL (Fin n) K) :
    ((inside₂ K n h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = (((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det)⁻¹ := by
  simp [inside₂, Matrix.det_transpose, Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Establish `hM : ((inside₂ K 0 h : GL (Fin 0) K) : Matrix (Fin 0) (Fin 0) K).transpose = ((h : GL (Fin 0) K) : Matrix (Fin 0) (Fin 0) K).transpose` using `Subsingleton.elim _ _`. Establish `hg : g = f` using `by simpa [funCof_zero] using hc`. Substitute `hg` using the available equality.

Simplify using `[funCof_zero, DomWeight.detShift, detPow, hM]`. Consider the case `succ m => set A : Matrix (Fin (m + 1)) (Fin (m + 1)) K := ((h : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) with hA`. Establish `hdet : IsUnit A.det` using `(Matrix.isUnit_iff_isUnit_det _).1 h.isUnit`. Establish `hD : A.det ≠ 0` using `hdet.ne_zero`. Establish `hH : IsUnit (A.transpose⁻¹).det`.

Rewrite using `[Matrix.det_nonsing_inv, Matrix.det_transpose, Ring.inverse_eq_inv']`. Conclude with `(isUnit_iff_ne_zero.2 (inv_ne_zero hD))`. Establish `h1` using `Eqv.cofRel_rowAct K m l.natW A.transpose⁻¹ hH f hf g (by rw [CofRel, ← funExp_succ]; exact hc)`. Establish `e1 : (A.transpose⁻¹)⁻¹ = A.transpose` using `Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hdet)`. Establish `e2 : (A.transpose⁻¹).transpose = ((inside₂ K (m + 1) h : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K).transpose`.

Simplify using `[inside₂, Matrix.coe_units_inv, hA, Matrix.transpose_nonsing_inv]`. Establish `e3 : (A.transpose⁻¹).det = A.det⁻¹`. Rewrite using `[Matrix.det_nonsing_inv, Matrix.det_transpose, Ring.inverse_eq_inv']`. Rewrite `h1` using `[CofRel, ← funExp_succ, e1, e2, e3]`. Establish `hν : (l.natW 0 : ℤ) = l.w 0 - l.w (Fin.last m)`.

Use `l.anti (Fin.zero_le (Fin.last m))` as an intermediate fact. Simplify using `only [DomWeight.natW, funDetShift_succ]`. Use linear arithmetic over natural numbers and integers. Establish `hs : detPow K (m + 1) (inside₂ K (m + 1) h) l.dual.detShift = detPow K (m + 1) h l.detShift * A.det⁻¹ ^ (-(l.natW 0 : ℤ))`. Rewrite using `[funDetPow_eq, funDetPow_eq, funDet_invTr, ← hA, inv_zpow', inv_zpow', ← zpow_add₀ hD]`.

Use `congr 1`. Simplify using `only [funDetShift_succ, funDual_w, Fin.rev_last]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[map_smul, ← h1, mul_smul_comm, mul_smul_comm, smul_smul, hs]`.
-/
theorem funPos_act (l : DomWeight n) (h : GL (Fin n) K) {f g : MP K n} (hf : f ∈ dualWeyl K n n l.natW)
    (hc : (genM K n).det ^ funExp l * g = cofAct K n f) :
    (genM K n).det ^ funExp l * (detPow K n (inside₂ K n h) l.dual.detShift •
        rowAct K ((inside₂ K n h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose g) =
      cofAct K n (detPow K n h l.detShift • rowAct K ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose f) := by
  cases n with
  | zero =>
    have hM : ((inside₂ K 0 h : GL (Fin 0) K) : Matrix (Fin 0) (Fin 0) K).transpose =
        ((h : GL (Fin 0) K) : Matrix (Fin 0) (Fin 0) K).transpose := Subsingleton.elim _ _
    have hg : g = f := by simpa [funCof_zero] using hc
    subst hg
    simp [funCof_zero, DomWeight.detShift, detPow, hM]
  | succ m =>
    set A : Matrix (Fin (m + 1)) (Fin (m + 1)) K := ((h : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) with hA
    have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
    have hD : A.det ≠ 0 := hdet.ne_zero
    have hH : IsUnit (A.transpose⁻¹).det := by
      rw [Matrix.det_nonsing_inv, Matrix.det_transpose, Ring.inverse_eq_inv']
      exact (isUnit_iff_ne_zero.2 (inv_ne_zero hD))
    have h1 := Eqv.cofRel_rowAct K m l.natW A.transpose⁻¹ hH f hf g (by rw [CofRel, ← funExp_succ]; exact hc)
    have e1 : (A.transpose⁻¹)⁻¹ = A.transpose :=
      Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hdet)
    have e2 : (A.transpose⁻¹).transpose = ((inside₂ K (m + 1) h : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K).transpose := by
      simp [inside₂, Matrix.coe_units_inv, hA, Matrix.transpose_nonsing_inv]
    have e3 : (A.transpose⁻¹).det = A.det⁻¹ := by
      rw [Matrix.det_nonsing_inv, Matrix.det_transpose, Ring.inverse_eq_inv']
    rw [CofRel, ← funExp_succ, e1, e2, e3] at h1
    have hν : (l.natW 0 : ℤ) = l.w 0 - l.w (Fin.last m) := by
      have := l.anti (Fin.zero_le (Fin.last m))
      simp only [DomWeight.natW, funDetShift_succ]
      omega
    have hs : detPow K (m + 1) (inside₂ K (m + 1) h) l.dual.detShift =
        detPow K (m + 1) h l.detShift * A.det⁻¹ ^ (-(l.natW 0 : ℤ)) := by
      rw [funDetPow_eq, funDetPow_eq, funDet_invTr, ← hA, inv_zpow', inv_zpow', ← zpow_add₀ hD]
      congr 1
      simp only [funDetShift_succ, funDual_w, Fin.rev_last]
      omega
    rw [map_smul, ← h1, mul_smul_comm, mul_smul_comm, smul_smul, hs]

end ActOne

section Main

variable {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (σ : ι → DomWeight n)

/- English proof (translation)
Unfold `IsFunForm FunRel`. Establish `hB : (∏ τ, frDet K n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (funFrDet_ne_zero τ)`. Establish `hA : ∏ τ, frDet K n τ ^ (∑ a, (σ τ).natW a) = (∏ τ, frDet K n τ ^ funExp (σ τ)) * ∏ τ, frDet K n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[← pow_add, funExp_add]`. Rewrite using `[hA]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `mul_right_cancel₀ hB` to reduce the goal to its premises.

Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isFunForm_iff_rel (F : VV K σ) (f : VV K fun τ => (σ τ).dual) :
    IsFunForm σ F f ↔ FunRel (fun τ => funExp (σ τ)) F.1 f.1 := by
  unfold IsFunForm FunRel
  have hB : (∏ τ, frDet K n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (funFrDet_ne_zero τ)
  have hA : ∏ τ, frDet K n τ ^ (∑ a, (σ τ).natW a) = (∏ τ, frDet K n τ ^ funExp (σ τ)) *
      ∏ τ, frDet K n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← pow_add, funExp_add]
  rw [hA]
  constructor
  · intro h
    apply mul_right_cancel₀ hB
    rw [← h]
    ring
  · intro h
    rw [← h]
    ring

/- English proof (translation)
Take `⟨G, hG, h⟩` from `funRel_exists (O := K) (fun τ => nablaSq K n (σ τ)) (fun τ => nablaSq K n (σ τ).dual) _ (fun τ => funPos_nabla K (σ τ)) F.1 F.2`. Conclude with `⟨⟨G, hG⟩, h⟩`.
-/
theorem funRel_exists_VV (F : VV K σ) :
    ∃ f : VV K (fun τ => (σ τ).dual), FunRel (fun τ => funExp (σ τ)) F.1 f.1 := by
  obtain ⟨G, hG, h⟩ := funRel_exists (O := K) (fun τ => nablaSq K n (σ τ)) (fun τ => nablaSq K n (σ τ).dual) _
    (fun τ => funPos_nabla K (σ τ)) F.1 F.2
  exact ⟨⟨G, hG⟩, h⟩

def funLin : VV K σ →ₗ[K] VV K (fun τ => (σ τ).dual) where
  toFun F := (funRel_exists_VV σ F).choose
  map_add' F F' := Subtype.ext (funRel_unique (funRel_exists_VV σ _).choose_spec
    ((funRel_exists_VV σ F).choose_spec.add (funRel_exists_VV σ F').choose_spec))
  map_smul' c F := Subtype.ext (funRel_unique (funRel_exists_VV σ _).choose_spec
    ((funRel_exists_VV σ F).choose_spec.smul c))

/- English proof (translation)
The claim follows from `(funRel_exists_VV σ F).choose_spec`.
-/
theorem funLin_rel (F : VV K σ) : FunRel (fun τ => funExp (σ τ)) F.1 (funLin σ F).1 :=
  (funRel_exists_VV σ F).choose_spec

/- English proof (translation)
Introduce `f`. Take `⟨F, hF, h⟩` from `funRel_exists_rev (O := K) (fun τ => nablaSq K n (σ τ)) (fun τ => nablaSq K n (σ τ).dual) _ (fun τ => funPos_nabla_rev K (σ τ)) f.1 f.2`. Conclude with `⟨⟨F, hF⟩, Subtype.ext (funRel_unique (funLin_rel σ _) h)⟩`.
-/
theorem funLin_surjective : Function.Surjective (funLin (K := K) σ) := by
  intro f
  obtain ⟨F, hF, h⟩ := funRel_exists_rev (O := K) (fun τ => nablaSq K n (σ τ)) (fun τ => nablaSq K n (σ τ).dual) _
    (fun τ => funPos_nabla_rev K (σ τ)) f.1 f.2
  exact ⟨⟨F, hF⟩, Subtype.ext (funRel_unique (funLin_rel σ _) h)⟩

/- English proof (translation)
The claim follows from `Module.Finite.of_basis (bVV K lam)`.
-/
theorem funVV_finite (lam : ι → DomWeight n) : Module.Finite K (VV K lam) := Module.Finite.of_basis (bVV K lam)

/- English proof (translation)
Use `funVV_finite (K := K) σ` as an intermediate fact. Use `funVV_finite (K := K) fun τ => (σ τ).dual` as an intermediate fact. Establish `h` using `LinearMap.finrank_range_le (funLin (K := K) σ)`. Rewrite `h` using `[LinearMap.range_eq_top.2 (funLin_surjective σ), finrank_top]`. Then use the resulting hypothesis.
-/
theorem funFinrank_le : Module.finrank K (VV K fun τ => (σ τ).dual) ≤ Module.finrank K (VV K σ) := by
  have := funVV_finite (K := K) σ
  have := funVV_finite (K := K) fun τ => (σ τ).dual
  have h := LinearMap.finrank_range_le (funLin (K := K) σ)
  rwa [LinearMap.range_eq_top.2 (funLin_surjective σ), finrank_top] at h

/- English proof (translation)
Use `funVV_finite (K := K) σ` as an intermediate fact. Use `funVV_finite (K := K) fun τ => (σ τ).dual` as an intermediate fact. Establish `dd : (fun τ => (σ τ).dual.dual) = σ` using `funext fun τ => funDual_dual (σ τ)`. Establish `h2 : Module.finrank K (VV K fun τ => (σ τ).dual.dual) ≤ Module.finrank K (VV K fun τ => (σ τ).dual)` using `funFinrank_le fun τ => (σ τ).dual`. Rewrite `h2` using `[dd]`.

Conclude with `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm (funFinrank_le σ) h2).symm).2 (funLin_surjective σ)`.
-/
theorem funLin_injective : Function.Injective (funLin (K := K) σ) := by
  have := funVV_finite (K := K) σ
  have := funVV_finite (K := K) fun τ => (σ τ).dual
  have dd : (fun τ => (σ τ).dual.dual) = σ := funext fun τ => funDual_dual (σ τ)
  have h2 : Module.finrank K (VV K fun τ => (σ τ).dual.dual) ≤ Module.finrank K (VV K fun τ => (σ τ).dual) :=
    funFinrank_le fun τ => (σ τ).dual
  rw [dd] at h2
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm (funFinrank_le σ) h2).symm).2
    (funLin_surjective σ)

def funEquiv : VV K σ ≃ₗ[K] VV K (fun τ => (σ τ).dual) :=
  LinearEquiv.ofBijective (funLin σ) ⟨funLin_injective σ, funLin_surjective σ⟩

/- English proof (translation)
The claim follows from `funLin_rel σ F`.
-/
theorem funEquiv_rel (F : VV K σ) : FunRel (fun τ => funExp (σ τ)) F.1 (funEquiv σ F).1 := funLin_rel σ F

/- English proof (translation)
The claim follows from `(isFunForm_iff_rel σ F _).2 (funEquiv_rel σ F)`.
-/
theorem isFunForm_funEquiv (F : VV K σ) : IsFunForm σ F (funEquiv σ F) :=
  (isFunForm_iff_rel σ F _).2 (funEquiv_rel σ F)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => Subtype.ext (funRel_unique ((isFunForm_iff_rel σ F f).1 h) (funEquiv_rel σ F)), fun h => h ▸ isFunForm_funEquiv σ F⟩`.
-/
theorem isFunForm_iff_eq (F : VV K σ) (f : VV K fun τ => (σ τ).dual) : IsFunForm σ F f ↔ f = funEquiv σ F :=
  ⟨fun h => Subtype.ext (funRel_unique ((isFunForm_iff_rel σ F f).1 h) (funEquiv_rel σ F)),
    fun h => h ▸ isFunForm_funEquiv σ F⟩

/- English proof (translation)
Introduce `F hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, rfl⟩` from `hx`. Use `choose G hG hG' using fun τ => funPos_nabla K (σ τ) (f τ) (hf τ)`.

Use `⟨ten G, funRel_ten hG', ?_⟩` and prove the remaining obligations. Use `show FunRel _ (actP σ g (ten f)) (actP _ (invTrK g) (ten G))`. Rewrite using `[funAct_ten, funAct_ten]`. Conclude with `funRel_ten fun τ => funPos_act (σ τ) (g τ) (hf τ) (hG' τ)`. Consider the case `zero => exact ⟨0, funRel_zero _, by simpa using funRel_zero _⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨G, e, e₂⟩` from `hx`. Take `⟨G', e', e₂'⟩` from `hy`. Conclude with `⟨G + G', e.add e', by simpa using e₂.add e₂'⟩`. Consider the case `smul c x _ hx`.

Take `⟨G, e, e₂⟩` from `hx`. Conclude with `⟨c • G, e.smul c, by simpa using e₂.smul c⟩`.
-/
theorem funRel_act (g : ι → GL (Fin n) K) : ∀ F ∈ VV K σ, ∃ G, FunRel (fun τ => funExp (σ τ)) F G ∧
    FunRel (fun τ => funExp (σ τ)) (actP σ g F) (actP (fun τ => (σ τ).dual) (invTrK g) G) := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    choose G hG hG' using fun τ => funPos_nabla K (σ τ) (f τ) (hf τ)
    refine ⟨ten G, funRel_ten hG', ?_⟩
    show FunRel _ (actP σ g (ten f)) (actP _ (invTrK g) (ten G))
    rw [funAct_ten, funAct_ten]
    exact funRel_ten fun τ => funPos_act (σ τ) (g τ) (hf τ) (hG' τ)
  | zero => exact ⟨0, funRel_zero _, by simpa using funRel_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨G, e, e₂⟩ := hx
    obtain ⟨G', e', e₂'⟩ := hy
    exact ⟨G + G', e.add e', by simpa using e₂.add e₂'⟩
  | smul c x _ hx =>
    obtain ⟨G, e, e₂⟩ := hx
    exact ⟨c • G, e.smul c, by simpa using e₂.smul c⟩

/- English proof (translation)
Take `⟨G, h1, h2⟩` from `funRel_act σ g F.1 F.2`. Establish `e : G = (funEquiv σ F).1` using `funRel_unique h1 (funEquiv_rel σ F)`. Substitute `e` using the available equality. Conclude with `Subtype.ext (funRel_unique (funEquiv_rel σ (rhoK σ g F)) h2)`.
-/
theorem funEquiv_rhoK (g : ι → GL (Fin n) K) (F : VV K σ) :
    funEquiv σ (rhoK σ g F) = rhoK (fun τ => (σ τ).dual) (invTrK g) (funEquiv σ F) := by
  obtain ⟨G, h1, h2⟩ := funRel_act σ g F.1 F.2
  have e : G = (funEquiv σ F).1 := funRel_unique h1 (funEquiv_rel σ F)
  subst e
  exact Subtype.ext (funRel_unique (funEquiv_rel σ (rhoK σ g F)) h2)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨G, hG, e⟩` from `funRel_exists M M' _ hf F.1 h`. Rewrite using `[funRel_unique (funEquiv_rel σ F) e]` and apply the resulting hypothesis. Introduce `h`.

Take `⟨F', hF', e⟩` from `funRel_exists_rev M M' _ hr _ h`. Establish `h1 : funEquiv σ ⟨F', hle _ hF'⟩ = funEquiv σ F` using `Subtype.ext (funRel_unique (funEquiv_rel σ ⟨F', hle _ hF'⟩) e)`. Establish `h2` using `(funEquiv σ).injective h1`. Rewrite using `[← h2]` and apply the resulting hypothesis.
-/
theorem funEquiv_mem_iff {O : Type} [CommRing O] [Algebra O K] (M M' : ι → Submodule O (MP K n))
    (hle : ∀ x ∈ tensorLat O K M, x ∈ VV K σ)
    (hf : ∀ τ, ∀ f ∈ M τ, ∃ g ∈ M' τ, (genM K n).det ^ funExp (σ τ) * g = cofAct K n f)
    (hr : ∀ τ, ∀ g ∈ M' τ, ∃ f ∈ M τ, (genM K n).det ^ funExp (σ τ) * g = cofAct K n f) (F : VV K σ) :
    F.1 ∈ tensorLat O K M ↔ (funEquiv σ F).1 ∈ tensorLat O K M' := by
  constructor
  · intro h
    obtain ⟨G, hG, e⟩ := funRel_exists M M' _ hf F.1 h
    rwa [funRel_unique (funEquiv_rel σ F) e]
  · intro h
    obtain ⟨F', hF', e⟩ := funRel_exists_rev M M' _ hr _ h
    have h1 : funEquiv σ ⟨F', hle _ hF'⟩ = funEquiv σ F :=
      Subtype.ext (funRel_unique (funEquiv_rel σ ⟨F', hle _ hF'⟩) e)
    have h2 := (funEquiv σ).injective h1
    rwa [← h2]

variable [NumberField K]

/- English proof (translation)
Introduce `x hx`. Establish `hle : nabStd K lam ≤ (VV K lam).restrictScalars (NumberField.RingOfIntegers K)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Use `Submodule.subset_span ⟨F, fun τ => ?_, rfl⟩` and prove the remaining obligations.

Take `⟨f, hf, e⟩` from `hF τ`. Rewrite using `[← e]`. Conclude with `dualWeylMap _ K _ _ _ _ _ hf`. Conclude with `hle hx`.
-/
theorem nabStd_mem_VV (lam : ι → DomWeight n) : ∀ x ∈ nabStd K lam, x ∈ VV K lam := by
  intro x hx
  have hle : nabStd K lam ≤ (VV K lam).restrictScalars (NumberField.RingOfIntegers K) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    refine Submodule.subset_span ⟨F, fun τ => ?_, rfl⟩
    obtain ⟨f, hf, e⟩ := hF τ
    rw [← e]
    exact dualWeylMap _ K _ _ _ _ _ hf
  exact hle hx

/- English proof (translation)
Introduce `x hx`. Establish `hle : delStd K lam ≤ (VV K lam).restrictScalars (NumberField.RingOfIntegers K)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨F, hF, rfl⟩`. Use `Submodule.subset_span ⟨F, fun τ => ?_, rfl⟩` and prove the remaining obligations.

Take `⟨f, hf, e⟩` from `hF τ`. Rewrite using `[← e]`. Conclude with `dualWeylMap _ K _ _ _ _ _ (weylLeDual _ _ _ _ _ (funNat_antitone _) hf)`. Conclude with `hle hx`.
-/
theorem delStd_mem_VV (lam : ι → DomWeight n) : ∀ x ∈ delStd K lam, x ∈ VV K lam := by
  intro x hx
  have hle : delStd K lam ≤ (VV K lam).restrictScalars (NumberField.RingOfIntegers K) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    refine Submodule.subset_span ⟨F, fun τ => ?_, rfl⟩
    obtain ⟨f, hf, e⟩ := hF τ
    rw [← e]
    exact dualWeylMap _ K _ _ _ _ _ (weylLeDual _ _ _ _ _ (funNat_antitone _) hf)
  exact hle hx

/- English proof (translation)
The claim follows from `funEquiv_mem_iff σ _ _ (nabStd_mem_VV σ) (fun τ => funMap_fwd _ _ (funPos_nabla _ (σ τ))) (fun τ => funMap_rev _ _ (funPos_nabla_rev _ (σ τ))) F`.
-/
theorem funEquiv_mem_nabStd (F : VV K σ) : F.1 ∈ nabStd K σ ↔ (funEquiv σ F).1 ∈ nabStd K fun τ => (σ τ).dual :=
  funEquiv_mem_iff σ _ _ (nabStd_mem_VV σ)
    (fun τ => funMap_fwd _ _ (funPos_nabla _ (σ τ))) (fun τ => funMap_rev _ _ (funPos_nabla_rev _ (σ τ))) F

/- English proof (translation)
The claim follows from `funEquiv_mem_iff σ _ _ (delStd_mem_VV σ) (fun τ => funMap_fwd _ _ (funPos_weyl _ (σ τ))) (fun τ => funMap_rev _ _ (funPos_weyl_rev _ (σ τ))) F`.
-/
theorem funEquiv_mem_delStd (F : VV K σ) : F.1 ∈ delStd K σ ↔ (funEquiv σ F).1 ∈ delStd K fun τ => (σ τ).dual :=
  funEquiv_mem_iff σ _ _ (delStd_mem_VV σ)
    (fun τ => funMap_fwd _ _ (funPos_weyl _ (σ τ))) (fun τ => funMap_rev _ _ (funPos_weyl_rev _ (σ τ))) F

omit [NumberField K] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨funEquiv σ, isFunForm_iff_eq σ, funEquiv_rhoK σ, fun F => ⟨funEquiv_mem_nabStd σ F, funEquiv_mem_delStd σ F⟩⟩`.
-/
theorem funForm : ∃ Φ : VV K σ ≃ₗ[K] VV K (fun τ => (σ τ).dual),
    (∀ F f, IsFunForm σ F f ↔ f = Φ F) ∧
    (∀ g F, Φ (rhoK σ g F) = rhoK (fun τ => (σ τ).dual) (invTrK g) (Φ F)) ∧
    ∀ [NumberField K] (F : VV K σ),
      (F.1 ∈ nabStd K σ ↔ (Φ F).1 ∈ nabStd K fun τ => (σ τ).dual) ∧
      (F.1 ∈ delStd K σ ↔ (Φ F).1 ∈ delStd K fun τ => (σ τ).dual) :=
  ⟨funEquiv σ, isFunForm_iff_eq σ, funEquiv_rhoK σ, fun F => ⟨funEquiv_mem_nabStd σ F, funEquiv_mem_delStd σ F⟩⟩

end Main

end GlobalTheory.FunObj
