import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau

noncomputable section

namespace GlobalTheory.HolDict.ShortVec

section Coord

open scoped TensorProduct

variable {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] {m : ℕ}

/- English proof (translation)
Use `choose n h0 h1 using h`. Use `⟨∏ i, n i, Finset.prod_pos fun i _ => h0 i, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]`. Conclude with `R.mul_mem (natCast_mem R _) (h1 i)`.
-/
theorem exists_common_denom {ι : Type} [Fintype ι] (R : Subring A) (x : ι → A)
    (h : ∀ i, ∃ d : ℕ, 0 < d ∧ (d : A) * x i ∈ R) : ∃ d : ℕ, 0 < d ∧ ∀ i, (d : A) * x i ∈ R := by
  classical
  choose n h0 h1 using h
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => h0 i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact R.mul_mem (natCast_mem R _) (h1 i)

/- English proof (translation)
Use `set B := Algebra.TensorProduct.basis A b`. Take `⟨d, hd, h⟩` from `exists_common_denom R (fun p : Fin n × Fin m × Fin m => B.repr (B p.2.1 * w p.1) p.2.2) fun _ => hR _`. Use `⟨d, hd, fun y e hy l => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]`. Use `R.sum_mem fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← B.sum_repr (y j), Finset.sum_mul, map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]`. Use `R.sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul, Nat.cast_mul, mul_comm (d : A), mul_mul_mul_comm]`. Conclude with `R.mul_mem (hy j k) (h (j, k, l))`.
-/
theorem exists_denom_dot (b : Module.Basis (Fin m) F E) (R : Subring A)
    (hR : ∀ a : A, ∃ d : ℕ, 0 < d ∧ (d : A) * a ∈ R) {n : ℕ} (w : Fin n → A ⊗[F] E) :
    ∃ d : ℕ, 0 < d ∧ ∀ (y : Fin n → A ⊗[F] E) (e : ℕ),
      (∀ j k, (e : A) * (Algebra.TensorProduct.basis A b).repr (y j) k ∈ R) →
      ∀ l, ((d * e : ℕ) : A) * (Algebra.TensorProduct.basis A b).repr (∑ j, y j * w j) l ∈ R := by
  set B := Algebra.TensorProduct.basis A b
  obtain ⟨d, hd, h⟩ := exists_common_denom R
    (fun p : Fin n × Fin m × Fin m => B.repr (B p.2.1 * w p.1) p.2.2) fun _ => hR _
  refine ⟨d, hd, fun y e hy l => ?_⟩
  rw [map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
  refine R.sum_mem fun j _ => ?_
  rw [← B.sum_repr (y j), Finset.sum_mul, map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
  refine R.sum_mem fun k _ => ?_
  rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul, Nat.cast_mul, mul_comm (d : A), mul_mul_mul_comm]
  exact R.mul_mem (hy j k) (h (j, k, l))

end Coord

section Arith

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

variable (F : Type) [Field F] [NumberField F]

def intRing : Subring (Af F) :=
  ⨅ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F).toSubring.comap (evalV F v).toRingHom

variable {F}

/- English proof (translation)
Rewrite using `[intRing, Subring.mem_iInf]`. Conclude with `forall_congr' fun v => (Valued.toNormedField.norm_le_one_iff (x := evalV F v a)).symm`.
-/
theorem mem_intRing {a : Af F} : a ∈ intRing F ↔ ∀ v, ‖evalV F v a‖ ≤ 1 := by
  rw [intRing, Subring.mem_iInf]
  exact forall_congr' fun v => (Valued.toNormedField.norm_le_one_iff (x := evalV F v a)).symm

/- English proof (translation)
Establish `hf : (Function.mulSupport fun v => max 1 ‖evalV F v a‖₊).Finite`. Use `(Filter.eventually_cofinite.1 a.2).subset fun v hv hv' => hv (max_eq_left ?_)` and prove the remaining obligations. Conclude with `Valued.toNormedField.norm_le_one_iff.2 hv'` after adjusting the coercions. Take `⟨d, hd, -, h⟩` from `GlobalTheory.SmoothForms.denom_global _ (fun v => le_max_left _ _) hf`. Use `⟨d, hd, mem_intRing.2 fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_natCast]`. Conclude with `h v _ (le_max_right _ _)`.
-/
theorem exists_denom_adele (a : Af F) : ∃ d : ℕ, 0 < d ∧ (d : Af F) * a ∈ intRing F := by
  have hf : (Function.mulSupport fun v => max 1 ‖evalV F v a‖₊).Finite := by
    refine (Filter.eventually_cofinite.1 a.2).subset fun v hv hv' => hv (max_eq_left ?_)
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 hv'
  obtain ⟨d, hd, -, h⟩ := GlobalTheory.SmoothForms.denom_global _ (fun v => le_max_left _ _) hf
  refine ⟨d, hd, mem_intRing.2 fun v => ?_⟩
  rw [map_mul, map_natCast]
  exact h v _ (le_max_right _ _)

/- English proof (translation)
Take `⟨r, rfl⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun v => by`. Establish `h1` using `mem_intRing.1 h v`. Rewrite `h1` using `[AlgHom.commutes]`. Rewrite using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x]`. Conclude with `Valued.toNormedField.norm_le_one_iff.1 h1`.

Conclude with `r.2`.
-/
theorem isIntegral_of_mem {x : F} (h : algebraMap F (Af F) x ∈ intRing F) : IsIntegral ℤ x := by
  obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun v => by
    have h1 := mem_intRing.1 h v
    rw [AlgHom.commutes] at h1
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x]
    exact Valued.toNormedField.norm_le_one_iff.1 h1
  exact r.2

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {m : ℕ}

/- English proof (translation)
Take `⟨d, hd, h⟩` from `exists_common_denom (integralClosure ℤ E).toSubring b fun k => by`. Take `⟨k, hk, r, hr⟩` from `GlobalTheory.SmoothForms.denom_exists_int (b k)`. Conclude with `⟨k, hk, hr ▸ r.2⟩`. Use `⟨d, hd, fun x e he hx hl => ?_⟩` and prove the remaining obligations. Establish `hi : IsIntegral ℤ (((d * e : ℕ) : E) * x)`.

Rewrite using `[← b.sum_repr x, Finset.mul_sum]`. Use `IsIntegral.sum _ fun k _ => ?_` and prove the remaining obligations. Establish `h1 : IsIntegral ℤ ((e : F) * b.repr x k)`. Apply `isIntegral_of_mem` to reduce the goal to its premises. Use `hl k` as an intermediate fact.

Rewrite `this` using `[Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `using this`. Establish `h2 : ((d * e : ℕ) : E) * b.repr x k • b k = algebraMap F E ((e : F) * b.repr x k) * ((d : E) * b k)`. Rewrite using `[Algebra.smul_def, map_mul, map_natCast]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `(h1.map (algebraMap F E).toIntAlgHom).mul (h k)`. Establish `h0 : (⟨_, hi⟩ : 𝓞 E) ≠ 0` using `fun h' => mul_ne_zero (Nat.cast_ne_zero.2 (Nat.mul_pos hd he).ne') hx (congrArg Subtype.val h')`. Take `⟨σ, hσ⟩` from `NumberField.exists_conjugate_one_le_norm h0`.

Use `⟨σ, hσ.trans_eq ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖σ (((d * e : ℕ) : E) * x)‖ = _`. Rewrite using `[map_mul, map_natCast, norm_mul, Complex.norm_natCast, Nat.cast_mul]`.
-/
theorem exists_emb_large (b : Module.Basis (Fin m) F E) :
    ∃ d : ℕ, 0 < d ∧ ∀ (x : E) (e : ℕ), 0 < e → x ≠ 0 →
      (∀ l, (e : Af F) * (Algebra.TensorProduct.basis (Af F) b).repr ((1 : Af F) ⊗ₜ[F] x) l ∈ intRing F) →
      ∃ σ : E →+* ℂ, 1 ≤ (d * e : ℝ) * ‖σ x‖ := by
  obtain ⟨d, hd, h⟩ := exists_common_denom (integralClosure ℤ E).toSubring b fun k => by
    obtain ⟨k, hk, r, hr⟩ := GlobalTheory.SmoothForms.denom_exists_int (b k)
    exact ⟨k, hk, hr ▸ r.2⟩
  refine ⟨d, hd, fun x e he hx hl => ?_⟩
  have hi : IsIntegral ℤ (((d * e : ℕ) : E) * x) := by
    rw [← b.sum_repr x, Finset.mul_sum]
    refine IsIntegral.sum _ fun k _ => ?_
    have h1 : IsIntegral ℤ ((e : F) * b.repr x k) := by
      apply isIntegral_of_mem
      have := hl k
      rw [Algebra.TensorProduct.basis_repr_tmul] at this
      simpa using this
    have h2 : ((d * e : ℕ) : E) * b.repr x k • b k = algebraMap F E ((e : F) * b.repr x k) * ((d : E) * b k) := by
      rw [Algebra.smul_def, map_mul, map_natCast]; push_cast; ring
    rw [h2]
    exact (h1.map (algebraMap F E).toIntAlgHom).mul (h k)
  have h0 : (⟨_, hi⟩ : 𝓞 E) ≠ 0 := fun h' =>
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.mul_pos hd he).ne') hx (congrArg Subtype.val h')
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm h0
  refine ⟨σ, hσ.trans_eq ?_⟩
  change ‖σ (((d * e : ℕ) : E) * x)‖ = _
  rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast, Nat.cast_mul]

end Arith

section Adelic

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

/- English proof (translation)
Proceed by induction on `hz using Subgroup.closure_induction with`. Consider the case `mem g hg`. Take `⟨a, ha⟩` from `hg`. Establish `h1 : (vecMulVec ξ ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* V.gram)).mulVec ξ = 0`. Rewrite using `[vecMulVec_mulVec, ← dotProduct_mulVec, hξ.2]`.

Simplify using the standard rewrite rules. Establish `h2 : ((vecMulVec ξ ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* V.gram)).map (incA D)).mulVec (fun i => incA D (ξ i)) = 0`. Use function extensionality and compare the values at `i`. Use `(RingHom.map_mulVec (incA D) _ ξ i).symm.trans ?_` and prove the remaining obligations. Rewrite using `[h1]`.

Conclude with `map_zero _`. Rewrite using `[sub_eq_iff_eq_add.1 ha, add_mulVec, smul_mulVec, h2, smul_zero, zero_add, one_mulVec]`. Consider the case `one => rw [map_one, Units.val_one, one_mulVec]`. Consider the case `mul x y _ _ hx hy => rw [map_mul, Units.val_mul, ← mulVec_mulVec, hy, hx]`. Consider the case `inv x _ hx => conv_lhs => rw [← hx]`.

Rewrite using `[mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]`.
-/
theorem mulVec_of_mem_ZI {ξ : Fin V.rank → D.host.E} (hξ : IsoVec V ξ) {z : GA D V} (hz : z ∈ ZI V ξ) :
    (matHom V z).1.mulVec (fun i => incA D (ξ i)) = fun i => incA D (ξ i) := by
  induction hz using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a, ha⟩ := hg
    have h1 : (vecMulVec ξ ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* V.gram)).mulVec ξ = 0 := by
      rw [vecMulVec_mulVec, ← dotProduct_mulVec, hξ.2]; simp
    have h2 : ((vecMulVec ξ ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* V.gram)).map (incA D)).mulVec
        (fun i => incA D (ξ i)) = 0 := by
      funext i
      refine (RingHom.map_mulVec (incA D) _ ξ i).symm.trans ?_
      rw [h1]; exact map_zero _
    rw [sub_eq_iff_eq_add.1 ha, add_mulVec, smul_mulVec, h2, smul_zero, zero_add, one_mulVec]
  | one => rw [map_one, Units.val_one, one_mulVec]
  | mul x y _ _ hx hy => rw [map_mul, Units.val_mul, ← mulVec_mulVec, hy, hx]
  | inv x _ hx =>
    conv_lhs => rw [← hx]
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]

/- English proof (translation)
Take `⟨γ', -, h'⟩` from `hγ`. Establish `h1 : (matHom V γ).1 = γ'.1.map (incA D)` using `(congrArg Units.val h').symm`. Use `⟨γ'.1.mulVec ξ, fun h => hξ.1 ?_, fun z hz a u B _ π => ?_⟩` and prove the remaining obligations. Use `congrArg (γ'⁻¹.1.mulVec ·) h` as an intermediate fact. Simplify `this` using `only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, mulVec_zero]`.

Rewrite using `[mulVec_mulVec, mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, show γ * (z * a * u) * u⁻¹ * a⁻¹ = γ * z by group]`. Use function extensionality and compare the values at `i`. Use `Eq.trans ?_ (RingHom.map_mulVec π _ (fun i => incA D (ξ i)) i)` and prove the remaining obligations. Rewrite using `[map_mul, Units.val_mul, ← mulVec_mulVec, mulVec_of_mem_ZI hξ hz, h1]`. Conclude with `congrArg π (RingHom.map_mulVec (incA D) _ ξ i)`.
-/
theorem exists_rat_vec {ξ : Fin V.rank → D.host.E} (hξ : IsoVec V ξ) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ η : Fin V.rank → D.host.E, η ≠ 0 ∧ ∀ z ∈ ZI V ξ, ∀ (a u : GA D V) {B : Type} [CommRing B]
      (π : AF D.host.F ⊗[D.host.F] D.host.E →+* B), (fun i => π (incA D (η i))) =
        ((matHom V (γ * (z * a * u))).1.map π).mulVec (((matHom V u⁻¹).1.map π).mulVec
          (((matHom V a⁻¹).1.map π).mulVec fun i => π (incA D (ξ i)))) := by
  obtain ⟨γ', -, h'⟩ := hγ
  have h1 : (matHom V γ).1 = γ'.1.map (incA D) := (congrArg Units.val h').symm
  refine ⟨γ'.1.mulVec ξ, fun h => hξ.1 ?_, fun z hz a u B _ π => ?_⟩
  · have := congrArg (γ'⁻¹.1.mulVec ·) h
    simpa only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, mulVec_zero] using this
  rw [mulVec_mulVec, mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, ← Units.val_mul, ← Units.val_mul, ← map_mul,
    ← map_mul, show γ * (z * a * u) * u⁻¹ * a⁻¹ = γ * z by group]
  funext i
  refine Eq.trans ?_ (RingHom.map_mulVec π _ (fun i => incA D (ξ i)) i)
  rw [map_mul, Units.val_mul, ← mulVec_mulVec, mulVec_of_mem_ZI hξ hz, h1]
  exact congrArg π (RingHom.map_mulVec (incA D) _ ξ i)

def finPr (D : D7) : AF D.host.F ⊗[D.host.F] D.host.E →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

def infPr (D : D7) : AF D.host.F ⊗[D.host.F] D.host.E →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem map_finPr (g : GA D V) : (matHom V g).1.map (finPr D) = finMat D.sp.cm.sig V.gram g := rfl

/- English proof (translation)
The claim follows from `congrArg Units.val (show finHom V u = 1 from hu)`.
-/
theorem map_finPr_of_mem {u : GA D V} (hu : u ∈ GinfC V) : (matHom V u).1.map (finPr D) = 1 :=
  congrArg Units.val (show finHom V u = 1 from hu)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finPr_incA (x : D.host.E) : finPr D (incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem map_infPr (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    (matHom V g).1.map (θ.comp (infPr D)) = archM V θ g := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem infPr_incA (x : D.host.E) : infPr D (incA D x) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x := rfl

/- English proof (translation)
Take `⟨d₁, hd₁, hle, hint⟩` from `GlobalTheory.SmoothForms.denom_global (fun v => finHt V v g) (fun v => le_max_left _ _) (finHt_mulSupport_finite V g)`. Establish `hH : (d₁ : NNReal) ≤ height θ V g` using `hle.trans (le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => le_max_left _ _))`. Use `⟨d₁, hd₁, by exact_mod_cast hH, fun i j k => mem_intRing.2 fun v => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g i j) k)‖₊ ≤ finHt V v g` using `(Finset.le_sup (f := fun p : Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) => ‖evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g p.1 p.2.1) p.2.2)‖₊) (Finset.mem_univ (i, j, k))).trans ((le_max_left _ _).trans (le_max_right _ _))`. Rewrite using `[map_mul, map_natCast]`.

Conclude with `hint v _ h1`.
-/
theorem exists_denom_le_height (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (g : GA D V) :
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ height θ V g ∧
      ∀ i j k, (d : Af D.host.F) * finCoord D (finMat D.sp.cm.sig V.gram g i j) k ∈ intRing D.host.F := by
  obtain ⟨d₁, hd₁, hle, hint⟩ := GlobalTheory.SmoothForms.denom_global (fun v => finHt V v g) (fun v => le_max_left _ _)
    (finHt_mulSupport_finite V g)
  have hH : (d₁ : NNReal) ≤ height θ V g :=
    hle.trans (le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => le_max_left _ _))
  refine ⟨d₁, hd₁, by exact_mod_cast hH, fun i j k => mem_intRing.2 fun v => ?_⟩
  have h1 : ‖evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g i j) k)‖₊ ≤ finHt V v g :=
    (Finset.le_sup (f := fun p : Fin V.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      ‖evalV D.host.F v (finCoord D (finMat D.sp.cm.sig V.gram g p.1 p.2.1) p.2.2)‖₊)
      (Finset.mem_univ (i, j, k))).trans ((le_max_left _ _).trans (le_max_right _ _))
  rw [map_mul, map_natCast]
  exact hint v _ h1

/- English proof (translation)
Take `⟨d₀, hd₀, h₀⟩` from `exists_denom_dot (Module.finBasis D.host.F D.host.E) (intRing D.host.F) exists_denom_adele w`. Take `⟨d₂, hd₂, h₂⟩` from `exists_emb_large (Module.finBasis D.host.F D.host.E)`. Use `⟨d₂ * d₀, by positivity, fun g x i hx hf => ?_⟩` and prove the remaining obligations. Take `⟨d₁, hd₁, hH, hint⟩` from `exists_denom_le_height θ g`. Take `⟨σ, hσ⟩` from `h₂ x (d₀ * d₁) (by positivity) hx fun l => by`.

Rewrite using `[hf]`. Conclude with `h₀ (fun j => finMat D.sp.cm.sig V.gram g i j) d₁ (hint i) l`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ, ‖σ x‖ = ‖tauE D τ x‖ := by`. Distinguish the cases in `h5 : ∃ ρ, tauE D ρ = ComplexEmbedding.conjugate σ`. Take `⟨ρ, h5⟩` from `h5`.

Conclude with `⟨ρ, by rw [h5]; exact (Complex.norm_conj _).symm⟩`. Take `⟨ρ, h5⟩` from `(GlobalTheory.PointAtPlace.tauE_cm σ).2 h5`. Conclude with `⟨ρ, by rw [h5]⟩`. Use `⟨τ, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_place_large (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : GA D V) (x : D.host.E) (i : Fin V.rank), x ≠ 0 →
      (1 : Af D.host.F) ⊗ₜ[D.host.F] x = ∑ j, finMat D.sp.cm.sig V.gram g i j * w j →
      ∃ τ, 1 ≤ C * height θ V g * ‖tauE D τ x‖ := by
  obtain ⟨d₀, hd₀, h₀⟩ := exists_denom_dot (Module.finBasis D.host.F D.host.E) (intRing D.host.F) exists_denom_adele w
  obtain ⟨d₂, hd₂, h₂⟩ := exists_emb_large (Module.finBasis D.host.F D.host.E)
  refine ⟨d₂ * d₀, by positivity, fun g x i hx hf => ?_⟩
  obtain ⟨d₁, hd₁, hH, hint⟩ := exists_denom_le_height θ g
  obtain ⟨σ, hσ⟩ := h₂ x (d₀ * d₁) (by positivity) hx fun l => by
    rw [hf]
    exact h₀ (fun j => finMat D.sp.cm.sig V.gram g i j) d₁ (hint i) l
  obtain ⟨τ, hτ⟩ : ∃ τ, ‖σ x‖ = ‖tauE D τ x‖ := by
    by_cases h5 : ∃ ρ, tauE D ρ = ComplexEmbedding.conjugate σ
    · obtain ⟨ρ, h5⟩ := h5
      exact ⟨ρ, by rw [h5]; exact (Complex.norm_conj _).symm⟩
    · obtain ⟨ρ, h5⟩ := (GlobalTheory.PointAtPlace.tauE_cm σ).2 h5
      exact ⟨ρ, by rw [h5]⟩
  refine ⟨τ, ?_⟩
  calc (1 : ℝ) ≤ d₂ * (d₀ * d₁) * ‖tauE D τ x‖ := by rw [← hτ]; exact_mod_cast hσ
    _ ≤ d₂ * (d₀ * height θ V g) * ‖tauE D τ x‖ := by gcongr
    _ = _ := by ring

/- English proof (translation)
Establish `hδ0 : 0 ≤ δ` using `(norm_nonneg _).trans (hδ i)`. Establish `h1 : ∀ j, ‖archM V (θ τ) g i j‖ ≤ height θ V g` using `fun j => (GlobalTheory.SmoothForms.NormInf.norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g) i j).trans (NNReal.coe_le_coe.2 (((le_max_left _ _).trans (le_max_right _ _)).trans (GlobalTheory.SmoothForms.NormInf.infHt_le_height θ V τ g)))`. Express the relevant statement in the definitionally equal form `‖∑ j, archM V (θ τ) g i j * y j‖ ≤ _`. Use `(norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (height θ V g * δ : ℝ) fun j _ => ?_).trans ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul (h1 j) (hδ j) (norm_nonneg _) (NNReal.coe_nonneg _)`. Rewrite using `[Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_mulVec_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau) (g : GA D V)
    (y : Fin V.rank → ℂ) {δ : ℝ} (hδ : ∀ j, ‖y j‖ ≤ δ) (i : Fin V.rank) :
    ‖(archM V (θ τ) g).mulVec y i‖ ≤ (V.rank + 1) * (height θ V g * δ) := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ i)
  have h1 : ∀ j, ‖archM V (θ τ) g i j‖ ≤ height θ V g := fun j =>
    (GlobalTheory.SmoothForms.NormInf.norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g) i j).trans
      (NNReal.coe_le_coe.2 (((le_max_left _ _).trans (le_max_right _ _)).trans
        (GlobalTheory.SmoothForms.NormInf.infHt_le_height θ V τ g)))
  change ‖∑ j, archM V (θ τ) g i j * y j‖ ≤ _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (height θ V g * δ : ℝ) fun j _ => ?_).trans ?_)
  · rw [norm_mul]
    exact mul_le_mul (h1 j) (hδ j) (norm_nonneg _) (NNReal.coe_nonneg _)
  · rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    gcongr
    linarith

/- English proof (translation)
Rewrite using `[archM, show infHom V a = 1 from ha, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem archM_of_mem (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {a : GA D V} (ha : a ∈ GfC V) :
    archM V θ a = 1 := by
  rw [archM, show infHom V a = 1 from ha, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
The claim follows from `(Matrix.inv_eq_left_inv (by rw [← GlobalTheory.PointAtPlace.archM_mul, inv_mul_cancel, GlobalTheory.PointAtPlace.archM_one])).symm`.
-/
theorem archM_inv (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (u : GA D V) :
    archM V θ u⁻¹ = (archM V θ u)⁻¹ := (Matrix.inv_eq_left_inv (by
  rw [← GlobalTheory.PointAtPlace.archM_mul, inv_mul_cancel, GlobalTheory.PointAtPlace.archM_one])).symm

/- English proof (translation)
Take `⟨C, hC, h₀⟩` from `exists_place_large (V := V) θ (((matHom V a⁻¹).1.map (finPr D)).mulVec fun i => finPr D (incA D (ξ i)))`. Use `⟨C * (V.rank + 1), by positivity, fun γ hγ z hz u hu δ hδ => ?_⟩` and prove the remaining obligations. Take `⟨η, hη, h⟩` from `exists_rat_vec hξ hγ`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hη`. Establish `hf` using `congrFun (h z hz a u (finPr D)) i`.

Rewrite `hf` using `[map_finPr_of_mem ((GinfC V).inv_mem hu), one_mulVec, map_finPr (γ * (z * a * u)), finPr_incA]`. Take `⟨τ, hτ⟩` from `h₀ (γ * (z * a * u)) (η i) i hi hf`. Establish `he : ∀ x, ((θ τ).comp (infPr D)) (incA D x) = tauE D τ x` using `fun x => by`. Rewrite using `[RingHom.comp_apply, infPr_incA]`. Conclude with `(hθ τ).1 x`.

Establish `hr` using `congrFun (h z hz a u ((θ τ).comp (infPr D))) i`. Rewrite using `[map_infPr, map_infPr, map_infPr, archM_of_mem _ ((GfC V).inv_mem ha), one_mulVec, archM_inv, he,`. Use function extensionality and compare the values at `fun i => he (ξ i)] at hr`. Establish `hb` using `norm_mulVec_le θ τ (γ * (z * a * u)) _ (hδ τ) i`. Rewrite `hb` using `[← hr]`.

Generalize the expression as in `(height θ V (γ * (z * a * u))) = H at hb hτ ⊢`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_bound (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    {ξ : Fin V.rank → D.host.E} (hξ : IsoVec V ξ) {a : GA D V} (ha : a ∈ GfC V) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ ∈ GQ V, ∀ z ∈ ZI V ξ, ∀ u ∈ GinfC V, ∀ δ : ℝ,
      (∀ τ i, ‖((archM V (θ τ) u)⁻¹.mulVec (fun j => tauE D τ (ξ j))) i‖ ≤ δ) →
      1 ≤ C * (δ * (height θ V (γ * (z * a * u)) : ℝ) ^ 2) := by
  obtain ⟨C, hC, h₀⟩ := exists_place_large (V := V) θ
    (((matHom V a⁻¹).1.map (finPr D)).mulVec fun i => finPr D (incA D (ξ i)))
  refine ⟨C * (V.rank + 1), by positivity, fun γ hγ z hz u hu δ hδ => ?_⟩
  obtain ⟨η, hη, h⟩ := exists_rat_vec hξ hγ
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hη
  have hf := congrFun (h z hz a u (finPr D)) i
  rw [map_finPr_of_mem ((GinfC V).inv_mem hu), one_mulVec, map_finPr (γ * (z * a * u)), finPr_incA] at hf
  obtain ⟨τ, hτ⟩ := h₀ (γ * (z * a * u)) (η i) i hi hf
  have he : ∀ x, ((θ τ).comp (infPr D)) (incA D x) = tauE D τ x := fun x => by
    rw [RingHom.comp_apply, infPr_incA]; exact (hθ τ).1 x
  have hr := congrFun (h z hz a u ((θ τ).comp (infPr D))) i
  rw [map_infPr, map_infPr, map_infPr, archM_of_mem _ ((GfC V).inv_mem ha), one_mulVec, archM_inv, he,
    funext fun i => he (ξ i)] at hr
  have hb := norm_mulVec_le θ τ (γ * (z * a * u)) _ (hδ τ) i
  rw [← hr] at hb
  generalize (height θ V (γ * (z * a * u))) = H at hb hτ ⊢
  calc (1 : ℝ) ≤ _ := hτ
    _ ≤ C * H * ((V.rank + 1) * (H * δ)) := by gcongr
    _ = _ := by ring

end Adelic

end GlobalTheory.HolDict.ShortVec

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

/- English proof (translation)
Introduce `D θ V hθ ξ hξ a ha`. Take `⟨C, hC, h⟩` from `ShortVec.exists_bound θ hθ hξ ha`. Use `⟨(4 * C)⁻¹, 2, by positivity, fun z hz u hu δ hδ _ hb => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, hle⟩` from `GlobalTheory.CuspDecay.exists_height_le (θ := θ) (z * a * u)`. Establish `h1 : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V (γ * (z * a * u)) : ℝ) ≤ 2 * (GlobalTheory.CuspDecay.quotHeight θ V (z * a * u) : ℝ)`.

Conclude with `hle` after adjusting the coercions. Rewrite using `[inv_le_iff_one_le_mul₀' (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem quotHeight_lower_bound : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → ∀ a ∈ GfC V, ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ z ∈ ZI V ξ, ∀ u ∈ GinfC V, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∀ τ i, ‖((archM V (θ τ) u)⁻¹.mulVec (fun j => tauE D τ (ξ j))) i‖ ≤ δ) → c ≤ δ * (GlobalTheory.CuspDecay.quotHeight θ V (z * a * u) : ℝ) ^ N := by
  intro D θ V hθ ξ hξ a ha
  obtain ⟨C, hC, h⟩ := ShortVec.exists_bound θ hθ hξ ha
  refine ⟨(4 * C)⁻¹, 2, by positivity, fun z hz u hu δ hδ _ hb => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := GlobalTheory.CuspDecay.exists_height_le (θ := θ) (z * a * u)
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V (γ * (z * a * u)) : ℝ) ≤ 2 * (GlobalTheory.CuspDecay.quotHeight θ V (z * a * u) : ℝ) := by
    exact_mod_cast hle
  rw [inv_le_iff_one_le_mul₀' (by positivity)]
  calc (1 : ℝ) ≤ _ := h γ hγ z hz u hu δ hb
    _ ≤ C * (δ * (2 * (GlobalTheory.CuspDecay.quotHeight θ V (z * a * u) : ℝ)) ^ 2) := by gcongr
    _ = _ := by ring

end GlobalTheory.HolDict

end
