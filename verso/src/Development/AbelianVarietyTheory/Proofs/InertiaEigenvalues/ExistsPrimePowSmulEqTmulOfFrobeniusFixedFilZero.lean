import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrisFixedLattice

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v m => simp`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
theorem coordLeft_lTensor {R : Type} [CommRing R] {V M N : Type}
    [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {ι : Type} [DecidableEq ι] (b : Module.Basis ι R V) (f : M →ₗ[R] N) (x : V ⊗[R] M) (i : ι) :
    equivFinsuppOfBasisLeft b (f.lTensor V x) i = f (equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v m => simp`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
theorem coordRight_map {R : Type} [CommRing R] {M P N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    {κ : Type} [DecidableEq κ] (b : Module.Basis κ R N) (f : M →ₗ[R] P) (x : M ⊗[R] N) (j : κ) :
    equivFinsuppOfBasisRight b (TensorProduct.map f LinearMap.id x) j = f (equivFinsuppOfBasisRight b x j) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus' (I := Ideal.span {(l : R)}) _ fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a)`. Establish `e : a = (a.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * c` using `by rw [← hc]; ring`.

Use `⟨f c - g c, ?_⟩` and prove the remaining obligations. Establish `hf` using `congrArg f e`. Establish `hg` using `congrArg g e`. Rewrite `hf`, `hg` using `[map_add, map_mul, map_pow, map_natCast, map_natCast]`. Rewrite using `[hf, hg]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem padicInt_ringHom_ext_pt {R : Type} [CommRing R] [IsHausdorff (Ideal.span {(l : R)}) R]
    (f g : ℤ_[l] →+* R) (a : ℤ_[l]) : f a = g a := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {(l : R)}) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a)
  have e : a = (a.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * c := by rw [← hc]; ring
  refine ⟨f c - g c, ?_⟩
  have hf := congrArg f e
  have hg := congrArg g e
  rw [map_add, map_mul, map_pow, map_natCast, map_natCast] at hf hg
  rw [hf, hg]
  ring

/- English proof (translation)
The claim follows from `padicInt_ringHom_ext_pt (R := WittVector l (Per.Fl l)) (Per.zA l) _ a`.
-/
theorem zA_eq_algebraMap_pt (a : ℤ_[l]) : Per.zA l a = algebraMap ℤ_[l] (Ainf l) a :=
  padicInt_ringHom_ext_pt (R := WittVector l (Per.Fl l)) (Per.zA l) _ a

/- English proof (translation)
Rewrite using `[zA_eq_algebraMap_pt]`. Conclude with `GlobalTheory.MemLoc.ULaws.iota_aB C _`.
-/
theorem iota_algebraMap_pt (C : GlobalTheory.MemLoc.Core l) (a : ℤ_[l]) :
    C.ι (algebraMap ℤ_[l] (Per.Bcris l) a) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (Per.zA l a)) := by
  rw [zA_eq_algebraMap_pt]
  exact GlobalTheory.MemLoc.ULaws.iota_aB C _

def filZero (C : GlobalTheory.MemLoc.Core l) : Submodule ℤ_[l] (Per.Bcris l) where
  carrier := {b | C.ι b ∈ Per.FilD l 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact add_mem ha hb
  smul_mem' := by
    intro a b hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Algebra.smul_def, map_mul]
    have e : C.ι (algebraMap ℤ_[l] (Per.Bcris l) a) =
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (Per.zA l a)) := iota_algebraMap_pt C a
    rw [e, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hb

/- English proof (translation)
Apply `GlobalTheory.MemLoc.ULaws.iota_injective C` to reduce the goal to its premises. Rewrite using `[iota_algebraMap_pt, ← C.o_sec.z]`. Conclude with `C.ι_u _`.
-/
theorem qB_padicInt (C : GlobalTheory.MemLoc.Core l) (a : ℤ_[l]) :
    C.qB (a : ℚ_[l]) = algebraMap ℤ_[l] (Per.Bcris l) a := by
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [iota_algebraMap_pt, ← C.o_sec.z]
  exact C.ι_u _

/- English proof (translation)
Establish `hl : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Rewrite using `[norm_mul, norm_pow, Padic.norm_p, inv_pow]`. Rewrite using `[inv_mul_le_iff₀ (pow_pos hl N), mul_one]`. Conclude with `h`.
-/
theorem exists_padicInt_of_norm_le (q : ℚ_[l]) (N : ℕ) (h : ‖q‖ ≤ (l : ℝ) ^ N) :
    ‖(l : ℚ_[l]) ^ N * q‖ ≤ 1 := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
  rw [inv_mul_le_iff₀ (pow_pos hl N), mul_one]
  exact h

end GlobalTheory.CrisFixedLattice

namespace GlobalTheory.CrisFixedLattice

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem frobOB_eq_lTensor {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (x : OB l O) : frobOB l O x = (frobB l).toLinearMap.lTensor O x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Introduce `hF l _ O K _ _ _ _ _ _ _ G _ _ T C z hφ hz`. Break down `subsingleton_or_nontrivial O with hO | hO` into its components or cases. Use `haveI := Module.subsingleton O (TW (OB l O) T)`. Conclude with `⟨0, 0, Subsingleton.elim _ _⟩`. Use `haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg`.

Use `haveI : Module.Free O ↥T.L.T := T.L.free`. Set `bO` to `Module.Free.chooseBasis ℤ_[l] O`. Set `bM` to `Module.Free.chooseBasis O ↥T.L.T`. Set `eR` to `TensorProduct.equivFinsuppOfBasisRight (M := OB l O) bM`. Set `eL` to `TensorProduct.equivFinsuppOfBasisLeft (N := Per.Bcris l) bO`.

Set `c` to `fun j i => eL (eR z j) i`. Establish `hcφ : ∀ j i, Per.φB l (c j i) = c j i`. Introduce `j i`. Establish `h1 : eR (TWmap (frobOB l O) T z) j = frobOB l O (eR z j)` using `coordRight_map bM (frobOB l O).toLinearMap z j`. Rewrite `h1` using `[hφ, frobOB_eq_lTensor]`.

Establish `h2 : c j i = eL ((frobB l).toLinearMap.lTensor O (eR z j)) i` using `congrArg (fun w => eL w i) h1`. Rewrite `h2` using `[coordLeft_lTensor]`. Conclude with `h2.symm`. Set `F0` to `filZero C`. Set `RQ : Submodule ℤ_[l] (OB l O)` to `LinearMap.range (F0.subtype.lTensor O)`.

Establish `hsmul : ∀ (o : O) (w : OB l O), w ∈ RQ → o • w ∈ RQ`. Introduce and unpack `o _ ⟨y, rfl⟩`. Use `⟨(LinearMap.mulLeft ℤ_[l] o).rTensor _ y, ?_⟩` and prove the remaining obligations. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a f => simp [TensorProduct.smul_tmul']`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, smul_add]`. Establish `key : ∀ w, w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} → ∀ j, eR w j ∈ RQ`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem w' hw'`. Take `⟨β, x, hβ, rfl⟩` from `hw'`. Introduce `j`. Rewrite using `[TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]`. Use `hsmul _ _ ⟨(1 : O) ⊗ₜ[ℤ_[l]] (⟨β, hβ⟩ : F0), ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules. Consider the case `zero => intro j`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro j`. Rewrite using `[map_add, Finsupp.add_apply]`.

Conclude with `add_mem (hx j) (hy j)`. Consider the case `smul o x _ hx => intro j`. Rewrite using `[map_smul, Finsupp.smul_apply]`. Conclude with `hsmul o _ (hx j)`. Establish `hzR : ∀ j, eR z j ∈ RQ` using `key z hz`.

Establish `hcF : ∀ j i, C.ι (c j i) ∈ Per.FilD l 0`. Introduce `j i`. Take `⟨y, hy⟩` from `hzR j`. Establish `h` using `coordLeft_lTensor bO F0.subtype y i`. Simplify using `only [c]`.

Rewrite using `[← hy, h]`. Conclude with `(equivFinsuppOfBasisLeft bO y i).2`. Establish `hq : ∀ j i, ∃ q : ℚ_[l], C.qB q = c j i` using `fun j i => (hF l C).2.2.2.1 _ (hcφ j i) (hcF j i)`. Use `choose q hqc using hq`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`.

Take `⟨N, hN⟩` from `pow_unbounded_of_one_lt (∑ j, ∑ i, ‖q j i‖) hl1`. Establish `hb : ∀ j i, ‖(l : ℚ_[l]) ^ N * q j i‖ ≤ 1` using `fun j i => by`. Use `exists_padicInt_of_norm_le _ N (le_trans ?_ hN.le)` and prove the remaining obligations. Use `le_trans ?_ (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg (q j i)) (Finset.mem_univ j))` and prove the remaining obligations. Conclude with `Finset.single_le_sum (fun i _ => norm_nonneg (q j i)) (Finset.mem_univ i)`.

Set `a : _ → _ → ℤ_[l]` to `fun j i => ⟨(l : ℚ_[l]) ^ N * q j i, hb j i⟩`. Establish `ha : ∀ j i, ((l ^ N : ℕ) : Per.Bcris l) * c j i = algebraMap ℤ_[l] (Per.Bcris l) (a j i)`. Introduce `j i`. Rewrite using `[← qB_padicInt, ← hqc]`. Use `show _ = C.qB ((l : ℚ_[l]) ^ N * q j i)`.

Rewrite using `[map_mul, map_pow, map_natCast, Nat.cast_pow]`. Set `y : _ → O` to `fun j => bO.equivFun.symm (a j)`. Use `⟨N, bM.equivFun.symm y, ?_⟩` and prove the remaining obligations. Apply `eR.injective` to reduce the goal to its premises. Use extensionality with `j : 1`.

Rewrite using `[TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]`. Apply `eL.injective` to reduce the goal to its premises. Use extensionality with `i : 1`. Establish `e1 : bM.repr (bM.equivFun.symm y) j = y j`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`.

Rewrite using `[e1, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, Finsupp.smul_apply, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, ha, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]`. Establish `e2 : bO.repr (y j) i = a j i`. Simplify using `only [y]`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Rewrite using `[e2, Algebra.smul_def, mul_one]`.
-/
theorem exists_pow_smul_eq_one_tmul : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (z : TW (OB l O) T), TWmap (frobOB l O) T z = z → z ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} → ∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • z = (1 : OB l O) ⊗ₜ[O] x := by
  intro hF l _ O K _ _ _ _ _ _ _ G _ _ T C z hφ hz
  classical
  rcases subsingleton_or_nontrivial O with hO | hO
  · haveI := Module.subsingleton O (TW (OB l O) T)
    exact ⟨0, 0, Subsingleton.elim _ _⟩
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI : Module.Free O ↥T.L.T := T.L.free
  let bO := Module.Free.chooseBasis ℤ_[l] O
  let bM := Module.Free.chooseBasis O ↥T.L.T
  let eR := TensorProduct.equivFinsuppOfBasisRight (M := OB l O) bM
  let eL := TensorProduct.equivFinsuppOfBasisLeft (N := Per.Bcris l) bO
  let c := fun j i => eL (eR z j) i

  have hcφ : ∀ j i, Per.φB l (c j i) = c j i := by
    intro j i
    have h1 : eR (TWmap (frobOB l O) T z) j = frobOB l O (eR z j) :=
      coordRight_map bM (frobOB l O).toLinearMap z j
    rw [hφ, frobOB_eq_lTensor] at h1
    have h2 : c j i = eL ((frobB l).toLinearMap.lTensor O (eR z j)) i := congrArg (fun w => eL w i) h1
    rw [coordLeft_lTensor] at h2
    exact h2.symm

  let F0 := filZero C
  let RQ : Submodule ℤ_[l] (OB l O) := LinearMap.range (F0.subtype.lTensor O)
  have hsmul : ∀ (o : O) (w : OB l O), w ∈ RQ → o • w ∈ RQ := by
    rintro o _ ⟨y, rfl⟩
    refine ⟨(LinearMap.mulLeft ℤ_[l] o).rTensor _ y, ?_⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a f => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have key : ∀ w, w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} → ∀ j, eR w j ∈ RQ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w' hw' =>
      obtain ⟨β, x, hβ, rfl⟩ := hw'
      intro j
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
      refine hsmul _ _ ⟨(1 : O) ⊗ₜ[ℤ_[l]] (⟨β, hβ⟩ : F0), ?_⟩
      simp
    | zero => intro j; simp
    | add x y _ _ hx hy => intro j; rw [map_add, Finsupp.add_apply]; exact add_mem (hx j) (hy j)
    | smul o x _ hx => intro j; rw [map_smul, Finsupp.smul_apply]; exact hsmul o _ (hx j)
  have hzR : ∀ j, eR z j ∈ RQ := key z hz
  have hcF : ∀ j i, C.ι (c j i) ∈ Per.FilD l 0 := by
    intro j i
    obtain ⟨y, hy⟩ := hzR j
    have h := coordLeft_lTensor bO F0.subtype y i
    simp only [c]
    rw [← hy, h]
    exact (equivFinsuppOfBasisLeft bO y i).2

  have hq : ∀ j i, ∃ q : ℚ_[l], C.qB q = c j i := fun j i => (hF l C).2.2.2.1 _ (hcφ j i) (hcF j i)
  choose q hqc using hq

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ j, ∑ i, ‖q j i‖) hl1
  have hb : ∀ j i, ‖(l : ℚ_[l]) ^ N * q j i‖ ≤ 1 := fun j i => by
    refine exists_padicInt_of_norm_le _ N (le_trans ?_ hN.le)
    refine le_trans ?_ (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg (q j i))
      (Finset.mem_univ j))
    exact Finset.single_le_sum (fun i _ => norm_nonneg (q j i)) (Finset.mem_univ i)
  let a : _ → _ → ℤ_[l] := fun j i => ⟨(l : ℚ_[l]) ^ N * q j i, hb j i⟩
  have ha : ∀ j i, ((l ^ N : ℕ) : Per.Bcris l) * c j i = algebraMap ℤ_[l] (Per.Bcris l) (a j i) := by
    intro j i
    rw [← qB_padicInt, ← hqc]
    show _ = C.qB ((l : ℚ_[l]) ^ N * q j i)
    rw [map_mul, map_pow, map_natCast, Nat.cast_pow]
  let y : _ → O := fun j => bO.equivFun.symm (a j)
  refine ⟨N, bM.equivFun.symm y, ?_⟩
  apply eR.injective
  ext j : 1
  rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  apply eL.injective
  ext i : 1
  have e1 : bM.repr (bM.equivFun.symm y) j = y j := by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [e1, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, Finsupp.smul_apply, map_nsmul, Finsupp.smul_apply,
    nsmul_eq_mul, ha, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  have e2 : bO.repr (y j) i = a j i := by
    simp only [y]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [e2, Algebra.smul_def, mul_one]

end GlobalTheory.CrisFixedLattice
