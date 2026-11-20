import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import GroundTheory.PAdicHodge.LocalBridge
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import GroundTheory.LocalFields.LubinTateLimitGalois
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup GroundTheory.PAdicHodge
open scoped GroundTheory.PAdicHodge.CyclNorms
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.LTHodge.CharEx

section Abstract

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω]
  [Algebra K Ω] [ValuativeExtension K Ω]
variable {π : 𝒪[K]}

/- English proof (translation)
Assume the negation of the conclusion as `hy`. Establish `hy' : 1 ≤ valuation Ω y` using `not_lt.mp hy`. Establish `h1` using `valuation_aeval_ltPoly_of_one_le (L := Ω) hπ hy'`. Rewrite `h1` using `[aeval_ltPoly, h]`. Rewrite `hx` using `[h1]`.

Conclude with `absurd hx (not_lt.mpr (one_le_pow₀ hy'))`.
-/
theorem valuation_lt_one_of_eq (hπ : Irreducible π) {x y : Ω} (hx : valuation Ω x < 1)
    (h : algebraMap K Ω (π : K) * y + y ^ Nat.card 𝓀[K] = x) : valuation Ω y < 1 := by
  by_contra hy
  have hy' : 1 ≤ valuation Ω y := not_lt.mp hy
  have h1 := valuation_aeval_ltPoly_of_one_le (L := Ω) hπ hy'
  rw [aeval_ltPoly, h] at h1
  rw [h1] at hx
  exact absurd hx (not_lt.mpr (one_le_pow₀ hy'))

section AlgClosed

variable [IsAlgClosed Ω]

/- English proof (translation)
Set `P : Polynomial Ω` to `((ltPoly π).map (algebraMap 𝒪[K] K)).map (algebraMap K Ω)`. Establish `hq` using `one_lt_card_residueField' K`. Establish `hPm : P.Monic` using `((ltPoly_monic π).map _).map _`. Establish `hPd : P.natDegree = Nat.card 𝓀[K]`. Rewrite using `[Polynomial.natDegree_map, (ltPoly_monic π).natDegree_map, natDegree_ltPoly]`.

Establish `hdeg : 0 < P.degree`. Rewrite using `[Polynomial.degree_eq_natDegree hPm.ne_zero, hPd]`. Conclude with `(by omega : 0 < Nat.card 𝓀[K])` after adjusting the coercions. Take `⟨y, hy⟩` from `IsAlgClosed.exists_root (P - Polynomial.C x) (by`. Rewrite using `[Polynomial.degree_sub_C hdeg]`.

Conclude with `hdeg.ne')`. Establish `hy2 : algebraMap K Ω (π : K) * y + y ^ Nat.card 𝓀[K] = x`. Establish `h1 : Polynomial.eval y P = x`. Simplify `hy` using `[sub_eq_zero, Polynomial.IsRoot]`. Rewrite using `[← aeval_ltPoly, ← h1]`.

Simplify using `only [P, Polynomial.eval_map_algebraMap]`. Conclude with `⟨y, valuation_lt_one_of_eq hπ hx hy2, hy2⟩`.
-/
theorem exists_preimage (hπ : Irreducible π) {x : Ω} (hx : valuation Ω x < 1) :
    ∃ y : Ω, valuation Ω y < 1 ∧ algebraMap K Ω (π : K) * y + y ^ Nat.card 𝓀[K] = x := by
  let P : Polynomial Ω := ((ltPoly π).map (algebraMap 𝒪[K] K)).map (algebraMap K Ω)
  have hq := one_lt_card_residueField' K
  have hPm : P.Monic := ((ltPoly_monic π).map _).map _
  have hPd : P.natDegree = Nat.card 𝓀[K] := by
    rw [Polynomial.natDegree_map, (ltPoly_monic π).natDegree_map, natDegree_ltPoly]
  have hdeg : 0 < P.degree := by
    rw [Polynomial.degree_eq_natDegree hPm.ne_zero, hPd]
    exact_mod_cast (by omega : 0 < Nat.card 𝓀[K])
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (P - Polynomial.C x) (by
    rw [Polynomial.degree_sub_C hdeg]; exact hdeg.ne')
  have hy2 : algebraMap K Ω (π : K) * y + y ^ Nat.card 𝓀[K] = x := by
    have h1 : Polynomial.eval y P = x := by
      simpa [sub_eq_zero, Polynomial.IsRoot] using hy
    rw [← aeval_ltPoly, ← h1]
    simp only [P, Polynomial.eval_map_algebraMap]
  exact ⟨y, valuation_lt_one_of_eq hπ hx hy2, hy2⟩

/- English proof (translation)
Establish `hq` using `one_lt_card_residueField' K`. Use `set a : Ω := algebraMap K Ω (π : K) with ha`. Establish `ha0 : a ≠ 0`. Rewrite using `[ha, Ne, map_eq_zero]`. Conclude with `fun h => hπ.ne_zero (Subtype.ext h)`.

Establish `hd : Nat.card 𝓀[K] - 1 ≠ 0` using `by omega`. Establish `hdeg : 0 < (Polynomial.X ^ (Nat.card 𝓀[K] - 1) : Polynomial Ω).degree`. Rewrite using `[Polynomial.degree_X_pow]`. Conclude with `Nat.pos_of_ne_zero hd` after adjusting the coercions. Take `⟨y, hy⟩` from `IsAlgClosed.exists_root ((Polynomial.X ^ (Nat.card 𝓀[K] - 1) : Polynomial Ω) - Polynomial.C (-a)) (by`.

Rewrite using `[Polynomial.degree_sub_C hdeg]`. Conclude with `hdeg.ne')`. Establish `h1 : y ^ (Nat.card 𝓀[K] - 1) = -a`. Establish `h2 : y ^ (Nat.card 𝓀[K] - 1) + a = 0`. Simplify `hy` using `[sub_eq_zero, Polynomial.IsRoot]`.

Conclude with `eq_neg_of_add_eq_zero_left h2`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Rewrite `h1` using `[zero_pow hd]`. Conclude with `ha0 (neg_eq_zero.mp h1.symm)`.

Establish `hy2 : a * y + y ^ Nat.card 𝓀[K] = 0`. Establish `: y ^ Nat.card 𝓀[K] = y ^ (Nat.card 𝓀[K] - 1) * y`. Rewrite using `[← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[this, h1]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨y, hy0, valuation_lt_one_of_eq hπ (by simp) hy2, hy2⟩`.
-/
theorem exists_first_point (hπ : Irreducible π) :
    ∃ y : Ω, y ≠ 0 ∧ valuation Ω y < 1 ∧ algebraMap K Ω (π : K) * y + y ^ Nat.card 𝓀[K] = 0 := by
  have hq := one_lt_card_residueField' K
  set a : Ω := algebraMap K Ω (π : K) with ha
  have ha0 : a ≠ 0 := by
    rw [ha, Ne, map_eq_zero]
    exact fun h => hπ.ne_zero (Subtype.ext h)
  have hd : Nat.card 𝓀[K] - 1 ≠ 0 := by omega
  have hdeg : 0 < (Polynomial.X ^ (Nat.card 𝓀[K] - 1) : Polynomial Ω).degree := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast Nat.pos_of_ne_zero hd
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
    ((Polynomial.X ^ (Nat.card 𝓀[K] - 1) : Polynomial Ω) - Polynomial.C (-a)) (by
      rw [Polynomial.degree_sub_C hdeg]; exact hdeg.ne')
  have h1 : y ^ (Nat.card 𝓀[K] - 1) = -a := by
    have h2 : y ^ (Nat.card 𝓀[K] - 1) + a = 0 := by
      simpa [sub_eq_zero, Polynomial.IsRoot] using hy
    exact eq_neg_of_add_eq_zero_left h2
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hd] at h1
    exact ha0 (neg_eq_zero.mp h1.symm)
  have hy2 : a * y + y ^ Nat.card 𝓀[K] = 0 := by
    have : y ^ Nat.card 𝓀[K] = y ^ (Nat.card 𝓀[K] - 1) * y := by
      rw [← pow_succ]; congr 1; omega
    rw [this, h1]; ring
  exact ⟨y, hy0, valuation_lt_one_of_eq hπ (by simp) hy2, hy2⟩

/- English proof (translation)
Take `⟨y, hy0, hyv, hy⟩` from `exists_first_point (K := K) (Ω := Ω) hπ`. Set `D` to `{x : Ω // valuation Ω x < 1}`. Use `choose s hs hs' using fun x : D => exists_preimage (K := K) (Ω := Ω) hπ x.2`. Set `w : ℕ → D` to `fun n => Nat.rec ⟨y, hyv⟩ (fun _ x => ⟨s x, hs x⟩) n`. Use `⟨fun n => Nat.casesOn n 0 (fun m => (w m).1), rfl, hy0, fun n => ?_, fun n => ?_⟩` and prove the remaining obligations.

Consider the cases of `n with`. Consider the case `zero => simp`. Consider the case `succ m => exact (w m).2`. Consider the cases of `n with`. Consider the case `zero => exact hy`.

Consider the case `succ m => exact hs' (w m)`.
-/
theorem exists_compatible (hπ : Irreducible π) :
    ∃ z : ℕ → Ω, z 0 = 0 ∧ z 1 ≠ 0 ∧ (∀ n, valuation Ω (z n) < 1) ∧
      ∀ n, algebraMap K Ω (π : K) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[K] = z n := by
  obtain ⟨y, hy0, hyv, hy⟩ := exists_first_point (K := K) (Ω := Ω) hπ
  let D := {x : Ω // valuation Ω x < 1}
  choose s hs hs' using fun x : D => exists_preimage (K := K) (Ω := Ω) hπ x.2
  let w : ℕ → D := fun n => Nat.rec ⟨y, hyv⟩ (fun _ x => ⟨s x, hs x⟩) n
  refine ⟨fun n => Nat.casesOn n 0 (fun m => (w m).1), rfl, hy0, fun n => ?_, fun n => ?_⟩
  · cases n with
    | zero => simp
    | succ m => exact (w m).2
  · cases n with
    | zero => exact hy
    | succ m => exact hs' (w m)

end AlgClosed

variable [TopologicalSpace Ω] [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω]

/- English proof (translation)
Set `e : (Unit →₀ ℕ) ≃ ℕ` to `Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)`. Establish `h` using `hasSum_psEval' (K := K) (σ := Unit) φ (fun _ => x) fun _ => hx`. Establish `h2` using `e.symm.hasSum_iff.mpr h`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Establish `hk : e.symm k = Finsupp.single () k` using `e.symm_apply_eq.mpr (by simp [e, Equiv.funUnique])`. Simplify using `only [Function.comp_apply, hk, psTerm, Finsupp.prod_single_index, pow_zero]`. Both sides reduce to the same expression.
-/
theorem hasSum_coeff_mul_pow (φ : PowerSeries 𝒪[K]) {x : Ω} (hx : valuation Ω x < 1) :
    HasSum (fun k : ℕ => algebraMap K Ω ((PowerSeries.coeff k φ : 𝒪[K]) : K) * x ^ k)
      (psEval φ fun _ => x) := by
  classical
  let e : (Unit →₀ ℕ) ≃ ℕ := Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)
  have h := hasSum_psEval' (K := K) (σ := Unit) φ (fun _ => x) fun _ => hx
  have h2 := e.symm.hasSum_iff.mpr h
  convert h2 using 1
  funext k
  have hk : e.symm k = Finsupp.single () k := e.symm_apply_eq.mpr (by simp [e, Equiv.funUnique])
  simp only [Function.comp_apply, hk, psTerm, Finsupp.prod_single_index, pow_zero]
  rfl

/- English proof (translation)
Use `t2Space_of_isValuativeTopology Ω` as an intermediate fact. Proceed by induction on `n with`. Consider the case `zero`. Introduce `x hx`. Rewrite using `[mem_lubinTateTorsion, pow_zero, one_smul]`.

Conclude with `IdealPoint.ext (by rw [hx, h0]; rfl)`. Consider the case `succ n ih`. Introduce `x hx`. Establish `h1 : (π • x).val = z n`. Rewrite using `[lubinTate_uniformizer_smul_val, hx]`.

Express the relevant statement in the definitionally equal form `psEval ((ltPoly π : Polynomial 𝒪[K]) : PowerSeries 𝒪[K]) (fun _ => z (n + 1)) = z n`. Rewrite using `[psEval_polynomial, aeval_ltPoly]`. Conclude with `hs n`. Establish `h2` using `(mem_lubinTateTorsion _ _ _).mp (ih (π • x) h1)`. Rewrite using `[mem_lubinTateTorsion, pow_succ, mul_smul]`.

Conclude with `h2`.
-/
theorem mem_torsion (hπ : Irreducible π) {z : ℕ → Ω} (h0 : z 0 = 0)
    (hs : ∀ n, algebraMap K Ω (π : K) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[K] = z n) (n : ℕ) :
    ∀ x : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π)), x.val = z n →
      x ∈ lubinTateTorsion Ω (hπ := hπ) (isLubinTateSeries_ltPoly π) n := by
  have := t2Space_of_isValuativeTopology Ω
  induction n with
  | zero =>
    intro x hx
    rw [mem_lubinTateTorsion, pow_zero, one_smul]
    exact IdealPoint.ext (by rw [hx, h0]; rfl)
  | succ n ih =>
    intro x hx
    have h1 : (π • x).val = z n := by
      rw [lubinTate_uniformizer_smul_val, hx]
      change psEval ((ltPoly π : Polynomial 𝒪[K]) : PowerSeries 𝒪[K]) (fun _ => z (n + 1)) = z n
      rw [psEval_polynomial, aeval_ltPoly]
      exact hs n
    have h2 := (mem_lubinTateTorsion _ _ _).mp (ih (π • x) h1)
    rw [mem_lubinTateTorsion, pow_succ, mul_smul]
    exact h2

variable [IsSepClosed Ω] {f : PowerSeries 𝒪[K]} (hπ : Irreducible π) (hf : IsLubinTateSeries π f)

def unitChar : (Ω ≃ₐ[K] Ω) →* 𝒪[K]ˣ :=
  ((lubinTateLimitGalEquiv (Ω := Ω) hπ hf).symm.toMulEquiv : _ →* _).comp
    (AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ))

/- English proof (translation)
The claim follows from `(lubinTateLimitGalEquiv (Ω := Ω) hπ hf).symm.continuous.comp (InfiniteGalois.restrictNormalHom_continuous _)`.
-/
theorem continuous_unitChar : Continuous (unitChar (Ω := Ω) hπ hf) :=
  (lubinTateLimitGalEquiv (Ω := Ω) hπ hf).symm.continuous.comp
    (InfiniteGalois.restrictNormalHom_continuous _)

/- English proof (translation)
Establish `h` using `lubinTateLimitGalEquiv_apply hπ hf (unitChar hπ hf g) hx`. Establish `h2 : lubinTateLimitGalEquiv (Ω` using `Ω) hπ hf (unitChar hπ hf g) = AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ) g := (lubinTateLimitGalEquiv (Ω := Ω) hπ hf).apply_symm_apply _`. Rewrite using `[← h, h2]`. Conclude with `(AlgEquiv.restrictNormal_commutes g (lubinTateLimit Ω hπ) ⟨x.val, lubinTateField_le_lubinTateLimit hπ hf n (val_mem_lubinTateField hπ hf hx)⟩).symm`.
-/
theorem apply_eq_smul (g : Ω ≃ₐ[K] Ω) {n : ℕ} {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)}
    (hx : x ∈ lubinTateTorsion Ω hf n) :
    g x.val = (((unitChar hπ hf g : 𝒪[K]ˣ) : 𝒪[K]) • x).val := by
  have h := lubinTateLimitGalEquiv_apply hπ hf (unitChar hπ hf g) hx
  have h2 : lubinTateLimitGalEquiv (Ω := Ω) hπ hf (unitChar hπ hf g) =
      AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ) g :=
    (lubinTateLimitGalEquiv (Ω := Ω) hπ hf).apply_symm_apply _
  rw [← h, h2]
  exact (AlgEquiv.restrictNormal_commutes g (lubinTateLimit Ω hπ)
    ⟨x.val, lubinTateField_le_lubinTateLimit hπ hf n (val_mem_lubinTateField hπ hf hx)⟩).symm

end Abstract

section Concrete

variable {l : ℕ} [Fact l.Prime]

local instance finDim (K : FinExt l) : FiniteDimensional ℚ_[l] ↥K.1 := K.2

local instance valExt (K : FinExt l) : ValuativeExtension ↥K.1 (Om l) :=
  ⟨fun a b => by rw [CyclNorms.vle_iff_norm_le, subfield_vle_iff_norm_le]; rfl⟩

/- English proof (translation)
Rewrite using `[integer_eq_normInteger K.1, mem_normInteger]`. Both sides reduce to the same expression.
-/
theorem mem_integer_iff (K : FinExt l) (x : ↥K.1) : x ∈ 𝒪[↥K.1] ↔ ‖(x : Om l)‖ ≤ 1 := by
  rw [integer_eq_normInteger K.1, mem_normInteger]
  rfl

def intEquiv (K : FinExt l) : ↥(OL K) ≃+* 𝒪[↥K.1] where
  toFun x := ⟨x.1, (mem_integer_iff K _).mpr ((GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mp x.2)⟩
  invFun y := ⟨y.1, (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mpr ((mem_integer_iff K _).mp y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

def gal (K : FinExt l) : ↥(GK K) →* (Om l ≃ₐ[↥K.1] Om l) :=
  (IntermediateField.fixingSubgroupEquiv K.1).toMonoidHom

/- English proof (translation)
Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_one]`. Introduce `s hs`. Take `⟨E, hE, hEs⟩` from `(krullTopology_mem_nhds_one_iff ↥K.1 _ s).mp hs`. Establish `: FiniteDimensional ℚ_[l] (E.restrictScalars ℚ_[l])` using `(Module.Finite.trans ↥K.1 E : FiniteDimensional ℚ_[l] E)`.

Establish `hO : IsOpen ((Subtype.val : ↥(GK K) → GQ l) ⁻¹' ((E.restrictScalars ℚ_[l]).fixingSubgroup : Set (GQ l)))` using `(IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val`. Establish `h1 : (1 : ↥(GK K)) ∈ (Subtype.val : ↥(GK K) → GQ l) ⁻¹' ((E.restrictScalars ℚ_[l]).fixingSubgroup : Set (GQ l))` using `one_mem (E.restrictScalars ℚ_[l]).fixingSubgroup`. Use `Filter.mem_map.mpr (Filter.mem_of_superset (hO.mem_nhds h1) fun g hg => hEs ?_)` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`.

Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x hx`.
-/
theorem continuous_gal (K : FinExt l) : Continuous (gal K) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff ↥K.1 _ s).mp hs
  have : FiniteDimensional ℚ_[l] (E.restrictScalars ℚ_[l]) :=
    (Module.Finite.trans ↥K.1 E : FiniteDimensional ℚ_[l] E)
  have hO : IsOpen ((Subtype.val : ↥(GK K) → GQ l) ⁻¹'
      ((E.restrictScalars ℚ_[l]).fixingSubgroup : Set (GQ l))) :=
    (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val
  have h1 : (1 : ↥(GK K)) ∈ (Subtype.val : ↥(GK K) → GQ l) ⁻¹'
      ((E.restrictScalars ℚ_[l]).fixingSubgroup : Set (GQ l)) :=
    one_mem (E.restrictScalars ℚ_[l]).fixingSubgroup
  refine Filter.mem_map.mpr (Filter.mem_of_superset (hO.mem_nhds h1) fun g hg => hEs ?_)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg x hx

/- English proof (translation)
Establish `e1 : (↥(OL K) ⧸ Ideal.span {(intEquiv K).symm π}) ≃ (𝒪[↥K.1] ⧸ Ideal.span {π})` using `(Ideal.quotientEquiv (Ideal.span {(intEquiv K).symm π}) (Ideal.span {π}) (intEquiv K) (by rw [Ideal.map_span, Set.image_singleton]; simp)).toEquiv`. Establish `e2 : 𝓀[↥K.1] ≃ (𝒪[↥K.1] ⧸ Ideal.span {π})` using `(Ideal.quotEquivOfEq hπ.maximalIdeal_eq).toEquiv`. Conclude with `Nat.card_congr (e1.trans e2.symm)`.
-/
theorem card_quot (K : FinExt l) {π : 𝒪[↥K.1]} (hπ : Irreducible π) :
    Nat.card (↥(OL K) ⧸ Ideal.span {(intEquiv K).symm π}) = Nat.card 𝓀[↥K.1] := by
  have e1 : (↥(OL K) ⧸ Ideal.span {(intEquiv K).symm π}) ≃ (𝒪[↥K.1] ⧸ Ideal.span {π}) :=
    (Ideal.quotientEquiv (Ideal.span {(intEquiv K).symm π}) (Ideal.span {π}) (intEquiv K)
      (by rw [Ideal.map_span, Set.image_singleton]; simp)).toEquiv
  have e2 : 𝓀[↥K.1] ≃ (𝒪[↥K.1] ⧸ Ideal.span {π}) :=
    (Ideal.quotEquivOfEq hπ.maximalIdeal_eq).toEquiv
  exact Nat.card_congr (e1.trans e2.symm)

/- English proof (translation)
Rewrite using `[ltSeries, card_quot K hπ, ltPoly]`. Simplify using the standard rewrite rules.
-/
theorem map_ltSeries (K : FinExt l) {π : 𝒪[↥K.1]} (hπ : Irreducible π) :
    PowerSeries.map ((intEquiv K : ↥(OL K) ≃+* 𝒪[↥K.1]) : ↥(OL K) →+* 𝒪[↥K.1])
      (ltSeries ((intEquiv K).symm π)) = (ltPoly π : PowerSeries 𝒪[↥K.1]) := by
  rw [ltSeries, card_quot K hπ, ltPoly]
  simp

/- English proof (translation)
Establish `ha : ‖(((u : 𝒪[↥K.1]) : ↥K.1) : Om l)‖ ≤ 1` using `(mem_integer_iff K ((u : 𝒪[↥K.1]) : ↥K.1)).mp (SetLike.coe_mem (u : 𝒪[↥K.1]))`. Establish `hb : ‖((((u⁻¹ : 𝒪[↥K.1]ˣ) : 𝒪[↥K.1]) : ↥K.1) : Om l)‖ ≤ 1` using `(mem_integer_iff K (((u⁻¹ : 𝒪[↥K.1]ˣ) : 𝒪[↥K.1]) : ↥K.1)).mp (SetLike.coe_mem ((u⁻¹ : 𝒪[↥K.1]ˣ) : 𝒪[↥K.1]))`. Establish `hm : ‖(((u : 𝒪[↥K.1]) : ↥K.1) : Om l)‖ * ‖((((u⁻¹ : 𝒪[↥K.1]ˣ) : 𝒪[↥K.1]) : ↥K.1) : Om l)‖ = 1`. Rewrite using `[← norm_mul]`. Establish `h2` using `congrArg (fun v : 𝒪[↥K.1] => ((v : ↥K.1) : Om l)) (Units.mul_inv u)`.

Simplify using `only [MulMemClass.coe_mul, OneMemClass.coe_one] at h2`. Rewrite using `[h2, norm_one]`. Use `le_antisymm ha ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_unit (K : FinExt l) (u : 𝒪[↥K.1]ˣ) : ‖(((u : 𝒪[↥K.1]) : ↥K.1) : Om l)‖ = 1 := by
  have ha : ‖(((u : 𝒪[↥K.1]) : ↥K.1) : Om l)‖ ≤ 1 :=
    (mem_integer_iff K ((u : 𝒪[↥K.1]) : ↥K.1)).mp (SetLike.coe_mem (u : 𝒪[↥K.1]))
  have hb : ‖((((u⁻¹ : 𝒪[↥K.1]ˣ) : 𝒪[↥K.1]) : ↥K.1) : Om l)‖ ≤ 1 :=
    (mem_integer_iff K (((u⁻¹ : 𝒪[↥K.1]ˣ) : 𝒪[↥K.1]) : ↥K.1)).mp
      (SetLike.coe_mem ((u⁻¹ : 𝒪[↥K.1]ˣ) : 𝒪[↥K.1]))
  have hm : ‖(((u : 𝒪[↥K.1]) : ↥K.1) : Om l)‖ *
      ‖((((u⁻¹ : 𝒪[↥K.1]ˣ) : 𝒪[↥K.1]) : ↥K.1) : Om l)‖ = 1 := by
    rw [← norm_mul]
    have h2 := congrArg (fun v : 𝒪[↥K.1] => ((v : ↥K.1) : Om l)) (Units.mul_inv u)
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h2
    rw [h2, norm_one]
  refine le_antisymm ha ?_
  calc (1 : ℝ) = _ := hm.symm
    _ ≤ ‖(((u : 𝒪[↥K.1]) : ↥K.1) : Om l)‖ * 1 :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := mul_one _

/- English proof (translation)
The claim follows from `(AddMonoidHomClass.isometry_of_norm K.1.val fun _ => rfl).continuous`.
-/
theorem continuous_coe_field (K : FinExt l) : Continuous (fun x : ↥K.1 => (x : Om l)) :=
  (AddMonoidHomClass.isometry_of_norm K.1.val fun _ => rfl).continuous

/- English proof (translation)
The claim follows from `(continuous_coe_field K).comp (continuous_subtype_val.comp Units.continuous_val)`.
-/
theorem continuous_coe_unit (K : FinExt l) :
    Continuous fun u : 𝒪[↥K.1]ˣ => (((u : 𝒪[↥K.1]) : ↥K.1) : Om l) :=
  (continuous_coe_field K).comp (continuous_subtype_val.comp Units.continuous_val)

/- English proof (translation)
Establish `hf` using `isLubinTateSeries_ltPoly π`. Set `e : ↥(OL K) →+* 𝒪[↥K.1]` to `((intEquiv K : ↥(OL K) ≃+* 𝒪[↥K.1]) : ↥(OL K) →+* 𝒪[↥K.1])`. Establish `he : Function.Injective e` using `(intEquiv K).injective`. Establish `hFm : PowerSeries.map e (ltSeries ((intEquiv K).symm π)) = (ltPoly π : PowerSeries 𝒪[↥K.1])` using `map_ltSeries K hπ`. Establish `hF0 : PowerSeries.constantCoeff (ltSeries ((intEquiv K).symm π)) = 0`.

Apply `he` to reduce the goal to its premises. Establish `h2` using `hf.constantCoeff_eq_zero`. Rewrite `h2` using `[← hFm, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Rewrite using `[h2, map_zero]`. Set `Φ : PowerSeries 𝒪[↥K.1]` to `PowerSeries.map e φ`.

Establish `hΦ0 : PowerSeries.constantCoeff Φ = 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0, map_zero]`. Establish `hΦs : PowerSeries.subst Φ (ltPoly π : PowerSeries 𝒪[↥K.1]) = PowerSeries.subst (ltPoly π : PowerSeries 𝒪[↥K.1]) Φ`. Establish `h2 : MvPowerSeries.map e (PowerSeries.subst φ (ltSeries ((intEquiv K).symm π))) = MvPowerSeries.map e (PowerSeries.subst (ltSeries ((intEquiv K).symm π)) φ)` using `congrArg (MvPowerSeries.map e) hsub`. Rewrite `h2` using `[PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hφ0), PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF0)]`.

Express the relevant statement in the definitionally equal form `PowerSeries.subst Φ (PowerSeries.map e (ltSeries ((intEquiv K).symm π))) = PowerSeries.subst (PowerSeries.map e (ltSeries ((intEquiv K).symm π))) Φ at h2`. Rewrite `h2` using `[hFm]`. Conclude with `h2`. Establish `hΦe` using `eq_lubinTateHom_toPowerSeries hπ hf hf _ hΦ0 hφ1 hΦs`. Establish `hx` using `mem_torsion (Ω := Om l) hπ h0 hs n (IdealPoint.mk (z n) (hv n)) rfl`.

Establish `hg` using `apply_eq_smul hπ hf (gal K g) hx`. Establish `hsum` using `hasSum_coeff_mul_pow Φ (hv n)`. Establish `hval : psEval Φ (fun _ => z n) = (g : GQ l) (z n)`. Rewrite using `[hΦe]`. Conclude with `((hg.trans (lubinTate_smul_val hf _ _))).symm`.

Rewrite `hsum` using `[hval]`. Simplify using `only [Φ, PowerSeries.coeff_map] at hsum`. Conclude with `hsum`.
-/
theorem hasSum_of_series (K : FinExt l) {π : 𝒪[↥K.1]} (hπ : Irreducible π) {z : ℕ → Om l}
    (h0 : z 0 = 0) (hv : ∀ n, valuation (Om l) (z n) < 1)
    (hs : ∀ n, algebraMap ↥K.1 (Om l) (π : ↥K.1) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[↥K.1] = z n)
    (g : ↥(GK K)) (φ : PowerSeries ↥(OL K)) (hφ0 : PowerSeries.constantCoeff φ = 0)
    (hφ1 : PowerSeries.coeff 1 (PowerSeries.map
        ((intEquiv K : ↥(OL K) ≃+* 𝒪[↥K.1]) : ↥(OL K) →+* 𝒪[↥K.1]) φ) =
      ((unitChar (Ω := Om l) hπ (isLubinTateSeries_ltPoly π) (gal K g) : 𝒪[↥K.1]ˣ) : 𝒪[↥K.1]))
    (hsub : PowerSeries.subst φ (ltSeries ((intEquiv K).symm π)) =
      PowerSeries.subst (ltSeries ((intEquiv K).symm π)) φ) (n : ℕ) :
    HasSum (fun k : ℕ => (((PowerSeries.coeff k φ : ↥(OL K)) : ↥K.1) : Om l) * z n ^ k)
      ((g : GQ l) (z n)) := by
  have hf := isLubinTateSeries_ltPoly π
  let e : ↥(OL K) →+* 𝒪[↥K.1] := ((intEquiv K : ↥(OL K) ≃+* 𝒪[↥K.1]) : ↥(OL K) →+* 𝒪[↥K.1])
  have he : Function.Injective e := (intEquiv K).injective
  have hFm : PowerSeries.map e (ltSeries ((intEquiv K).symm π)) =
      (ltPoly π : PowerSeries 𝒪[↥K.1]) := map_ltSeries K hπ
  have hF0 : PowerSeries.constantCoeff (ltSeries ((intEquiv K).symm π)) = 0 := by
    apply he
    have h2 := hf.constantCoeff_eq_zero
    rw [← hFm, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] at h2
    rw [h2, map_zero]
  let Φ : PowerSeries 𝒪[↥K.1] := PowerSeries.map e φ
  have hΦ0 : PowerSeries.constantCoeff Φ = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hφ0, map_zero]
  have hΦs : PowerSeries.subst Φ (ltPoly π : PowerSeries 𝒪[↥K.1]) =
      PowerSeries.subst (ltPoly π : PowerSeries 𝒪[↥K.1]) Φ := by
    have h2 : MvPowerSeries.map e (PowerSeries.subst φ (ltSeries ((intEquiv K).symm π))) =
        MvPowerSeries.map e (PowerSeries.subst (ltSeries ((intEquiv K).symm π)) φ) :=
      congrArg (MvPowerSeries.map e) hsub
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hφ0),
      PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF0)] at h2
    change PowerSeries.subst Φ (PowerSeries.map e (ltSeries ((intEquiv K).symm π))) =
      PowerSeries.subst (PowerSeries.map e (ltSeries ((intEquiv K).symm π))) Φ at h2
    rw [hFm] at h2
    exact h2
  have hΦe := eq_lubinTateHom_toPowerSeries hπ hf hf _ hΦ0 hφ1 hΦs
  have hx := mem_torsion (Ω := Om l) hπ h0 hs n (IdealPoint.mk (z n) (hv n)) rfl
  have hg := apply_eq_smul hπ hf (gal K g) hx
  have hsum := hasSum_coeff_mul_pow Φ (hv n)
  have hval : psEval Φ (fun _ => z n) = (g : GQ l) (z n) := by
    rw [hΦe]
    exact ((hg.trans (lubinTate_smul_val hf _ _))).symm
  rw [hval] at hsum
  simp only [Φ, PowerSeries.coeff_map] at hsum
  exact hsum

end Concrete

/- English proof (translation)
Establish `: FiniteDimensional ℚ_[l] ↥K.1` using `K.2`. Establish `: ValuativeExtension ↥K.1 (Om l)` using `valExt K`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[↥K.1]`. Set `C : ↥(GK K) →* 𝒪[↥K.1]ˣ` to `(unitChar (Ω := Om l) hπ (isLubinTateSeries_ltPoly π)).comp (gal K)`. Establish `hC : Continuous C` using `(continuous_unitChar hπ _).comp (continuous_gal K)`.

Set `χ : ↥(GK K) →* (↥K.1)ˣ` to `(Units.map (𝒪[↥K.1].subtype : 𝒪[↥K.1] →+* ↥K.1).toMonoidHom).comp C`. Take `⟨z, h0, h1, hv, hs⟩` from `exists_compatible (K := ↥K.1) (Ω := Om l) hπ`. Use `⟨χ, ⟨(intEquiv K).symm π, z, ?_, h0, h1, ?_, ?_⟩, ?_, fun g => norm_unit K (C g)⟩` and prove the remaining obligations. Conclude with `(MulEquiv.irreducible_iff (intEquiv K).symm).mpr hπ`. Introduce `n`.

Rewrite using `[card_quot K hπ, add_comm]`. Conclude with `hs n`. Introduce `g φ hφ0 hφ1 hsub n`. Use `hasSum_of_series K hπ h0 hv hs g φ hφ0 ?_ hsub n` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[PowerSeries.coeff_map]`. Conclude with `hφ1`. Conclude with `(continuous_coe_unit K).comp hC`.
-/
theorem exists_ltChar {l : ℕ} [Fact l.Prime] (K : FinExt l) :
    ∃ χ : ↥(GK K) →* (↥K.1)ˣ, GlobalTheory.CompanionTheory.LTHodge.IsLTChar K χ ∧
      Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) ∧
      ∀ g, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ = 1 := by
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : ValuativeExtension ↥K.1 (Om l) := valExt K
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[↥K.1]
  let C : ↥(GK K) →* 𝒪[↥K.1]ˣ :=
    (unitChar (Ω := Om l) hπ (isLubinTateSeries_ltPoly π)).comp (gal K)
  have hC : Continuous C := (continuous_unitChar hπ _).comp (continuous_gal K)
  let χ : ↥(GK K) →* (↥K.1)ˣ := (Units.map (𝒪[↥K.1].subtype : 𝒪[↥K.1] →+* ↥K.1).toMonoidHom).comp C
  obtain ⟨z, h0, h1, hv, hs⟩ := exists_compatible (K := ↥K.1) (Ω := Om l) hπ
  refine ⟨χ, ⟨(intEquiv K).symm π, z, ?_, h0, h1, ?_, ?_⟩, ?_, fun g => norm_unit K (C g)⟩
  · exact (MulEquiv.irreducible_iff (intEquiv K).symm).mpr hπ
  · intro n
    rw [card_quot K hπ, add_comm]
    exact hs n
  · intro g φ hφ0 hφ1 hsub n
    refine hasSum_of_series K hπ h0 hv hs g φ hφ0 ?_ hsub n
    apply Subtype.ext
    rw [PowerSeries.coeff_map]
    exact hφ1
  · exact (continuous_coe_unit K).comp hC

end GlobalTheory.CompanionTheory.LTHodge.CharEx
