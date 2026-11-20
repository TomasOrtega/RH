import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Formalism.UG Formalism.UG.P Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.LevRead

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h1 : ∀ n : ℕ, Valued.v (afIso F E (1 ⊗ₜ[F] afsplitI (P.under (𝓞 F)) 1) P - algebraMap E _ (algebraMap F E 1)) ≤ WithZero.exp (-(n : ℤ))` using `fun n => (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 _ 1 P n (by rw [afsplitI_self, map_one, sub_self, map_zero]; exact zero_le')`. Rewrite `h1` using `[map_one (algebraMap F E), map_one (algebraMap E (P.adicCompletion E))]`. Express the relevant statement in the definitionally equal form `afIso F E (1 ⊗ₜ[F] afsplitI (P.under (𝓞 F)) 1) P = 1`. Assume the negation of the conclusion as `hne`. Establish `h0 : Valued.v (afIso F E (1 ⊗ₜ[F] afsplitI (P.under (𝓞 F)) 1) P - 1) ≠ 0`.

Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `sub_ne_zero.2 hne`. Establish `h2` using `h1 (1 - WithZero.log (Valued.v (afIso F E (1 ⊗ₜ[F] afsplitI (P.under (𝓞 F)) 1) P - 1))).toNat`. Use `conv_lhs at h2 => rw [← WithZero.exp_log h0]`. Rewrite `h2` using `[WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem adAt_eps (P : HeightOneSpectrum (𝓞 E)) : adAt F P (afsplitEps E (P.under (𝓞 F))) = 1 := by
  have h1 : ∀ n : ℕ, Valued.v (afIso F E (1 ⊗ₜ[F] afsplitI (P.under (𝓞 F)) 1) P - algebraMap E _ (algebraMap F E 1)) ≤
      WithZero.exp (-(n : ℤ)) :=
    fun n => (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 _ 1 P n
      (by rw [afsplitI_self, map_one, sub_self, map_zero]; exact zero_le')
  rw [map_one (algebraMap F E), map_one (algebraMap E (P.adicCompletion E))] at h1
  change afIso F E (1 ⊗ₜ[F] afsplitI (P.under (𝓞 F)) 1) P = 1
  by_contra hne
  have h0 : Valued.v (afIso F E (1 ⊗ₜ[F] afsplitI (P.under (𝓞 F)) 1) P - 1) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact sub_ne_zero.2 hne
  have h2 := h1 (1 - WithZero.log (Valued.v (afIso F E (1 ⊗ₜ[F] afsplitI (P.under (𝓞 F)) 1) P - 1))).toNat
  conv_lhs at h2 => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp] at h2
  omega

/- English proof (translation)
Substitute `hP` using the available equality. Rewrite using `[afsplit_decomp, map_mul, adAt_eps, one_mul]`.
-/
theorem adAt_IE {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)} (hP : P.under (𝓞 F) = v) (z : AfE F E) :
    adAt F P (afsplitIE v (prV (E := E) v z)) = adAt F P z := by
  subst hP
  rw [afsplit_decomp, map_mul, adAt_eps, one_mul]

/- English proof (translation)
Rewrite using `[← adAt_IE hP z, h, adAt_IE hP]`.
-/
theorem adAt_congr {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)} (hP : P.under (𝓞 F) = v) {z z' : AfE F E}
    (h : prV (E := E) v z = prV (E := E) v z') : adAt F P z = adAt F P z' := by
  rw [← adAt_IE hP z, h, adAt_IE hP]

/- English proof (translation)
Rewrite using `[← adAt_IE hP z]`. Conclude with `(mem_rInt_iff F E _).1 (afsplit_IE_int v _ h) P`.
-/
theorem valued_adAt_le {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)} (hP : P.under (𝓞 F) = v) {z : AfE F E}
    (h : prV (E := E) v z ∈ intV E v) : Valued.v (adAt F P z) ≤ 1 := by
  rw [← adAt_IE hP z]
  exact (mem_rInt_iff F E _).1 (afsplit_IE_int v _ h) P

variable {n : ℕ}

/- English proof (translation)
The claim follows from `adAt_congr hP (congrArg (fun x : GL (Fin n) (E ⊗[F] v.adicCompletion F) => ((x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) h)`.
-/
theorem bc_adAt_congr {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)} (hP : P.under (𝓞 F) = v)
    {a b : GL (Fin n) (AfE F E)} (h : bc (prV (E := E) v) a = bc (prV (E := E) v) b) (i j : Fin n) :
    adAt F P ((a : Matrix (Fin n) (Fin n) (AfE F E)) i j) = adAt F P ((b : Matrix (Fin n) (Fin n) (AfE F E)) i j) :=
  adAt_congr hP (congrArg (fun x : GL (Fin n) (E ⊗[F] v.adicCompletion F) =>
    ((x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) h)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[← sub_eq_zero]`. Use `afsplit_inj _ fun v => ?_` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero]`.

Conclude with `congrArg (fun x : GL (Fin n) (E ⊗[F] v.adicCompletion F) => ((x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) (h v)`.
-/
theorem gl_ext {a b : GL (Fin n) (AfE F E)} (h : ∀ v, bc (prV (E := E) v) a = bc (prV (E := E) v) b) : a = b := by
  apply Units.ext
  ext i j
  rw [← sub_eq_zero]
  refine afsplit_inj _ fun v => ?_
  rw [map_sub, sub_eq_zero]
  exact congrArg (fun x : GL (Fin n) (E ⊗[F] v.adicCompletion F) =>
    ((x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j) (h v)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[afsplit_coe_bc_prV, afsplitU_coe, afsplitC_prV_ne v w h, Units.val_one, Units.val_one]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem bc_afsplitU_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    bc (prV (E := E) w) (afsplitU v x 1) = 1 := by
  apply Units.ext
  rw [afsplit_coe_bc_prV, afsplitU_coe, afsplitC_prV_ne v w h, Units.val_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inl ⟨⟨_, r, rfl⟩, rfl⟩)`.
-/
theorem tmul_one_mem (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 E) :
    inclE (F := F) (v.adicCompletion F) (r : E) ∈ intV E v :=
  Subring.subset_closure (Or.inl ⟨⟨_, r, rfl⟩, rfl⟩)

/- English proof (translation)
The claim follows from `Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)`.
-/
theorem one_tmul_mem (v : HeightOneSpectrum (𝓞 F)) {a : v.adicCompletion F} (ha : a ∈ v.adicCompletionIntegers F) :
    (1 : E) ⊗ₜ[F] a ∈ intV E v :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

/- English proof (translation)
Rewrite using `[← valued_algebraMap, map_natCast (algebraMap (𝓞 F) F), map_natCast (algebraMap F (v.adicCompletion F))]`.
-/
theorem valued_natCast (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) :
    Valued.v (N : v.adicCompletion F) = v.valuation F (algebraMap (𝓞 F) F N) := by
  rw [← valued_algebraMap, map_natCast (algebraMap (𝓞 F) F), map_natCast (algebraMap F (v.adicCompletion F))]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`.

Introduce `b`. Take `⟨r, hr⟩` from `h1 z hz b`. Use `show inclE (F := F) (v.adicCompletion F) (z b) ∈ _`. Rewrite using `[hr]`. Conclude with `tmul_one_mem v r`.

Consider the case `zero => exact fun _ => zero_mem _`. Consider the case `add x y _ _ hx hy => exact fun b => add_mem (hx b) (hy b)`. Consider the case `smul a x _ hx => exact fun b => mul_mem a.2 (hx b)`. Introduce `hy`. Establish `hv : Valued.v (T : v.adicCompletion F) = 1`.

Rewrite using `[valued_natCast]`. Conclude with `CharValCompare.val_of_notMem hT`. Establish `h0 : (T : v.adicCompletion F) ≠ 0` using `fun h => by rw [h, map_zero] at hv; exact zero_ne_one hv`. Establish `hi : (T : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]`.

Establish `e1 : (1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹ * inclE (F` using `F) (v.adicCompletion F) (T : E) = 1 := by`. Rewrite using `[map_natCast, ← map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := v.adicCompletion F))]`. Use `show (1 : E) ⊗ₜ[F] _ * (1 : E) ⊗ₜ[F] _ = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ h0]`. Both sides reduce to the same expression.

Establish `e : y = ∑ j, (⟨_, mul_mem (hy j) (one_tmul_mem (E` using `E) v hi)⟩ : intV E v) • fun i => inclE (F := F) (v.adicCompletion F) ((Pi.single j (T : E) : Fin n → E) i) := by`. Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single i]`. Use `show _ = y i * _ * inclE (F := F) (v.adicCompletion F) ((Pi.single i (T : E) : Fin n → E) i)`. Rewrite using `[Pi.single_eq_same, mul_assoc, e1, mul_one]`.

Introduce `j _ hj show y j * _ * inclE (F := F) (v.adicCompletion F) ((Pi.single j (T : E) : Fin n → E) i) = 0`. Rewrite using `[Pi.single_eq_of_ne hj.symm, map_zero, mul_zero]`. Conclude with `fun h => absurd (Finset.mem_univ i) h`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h2 j, rfl⟩)`.
-/
theorem mem_latS_iff {v : HeightOneSpectrum (𝓞 F)} {L : Submodule (𝓞 E) (Fin n → E)} {T : ℕ} (hT : (T : 𝓞 F) ∉ v.asIdeal)
    (h1 : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 E, x j = r) (h2 : ∀ j, (Pi.single j (T : E) : Fin n → E) ∈ L)
    (y : Fin n → E ⊗[F] v.adicCompletion F) :
    y ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔ ∀ b, y b ∈ intV E v := by
  classical
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      intro b
      obtain ⟨r, hr⟩ := h1 z hz b
      show inclE (F := F) (v.adicCompletion F) (z b) ∈ _
      rw [hr]
      exact tmul_one_mem v r
    | zero => exact fun _ => zero_mem _
    | add x y _ _ hx hy => exact fun b => add_mem (hx b) (hy b)
    | smul a x _ hx => exact fun b => mul_mem a.2 (hx b)
  · intro hy
    have hv : Valued.v (T : v.adicCompletion F) = 1 := by
      rw [valued_natCast]
      exact CharValCompare.val_of_notMem hT
    have h0 : (T : v.adicCompletion F) ≠ 0 := fun h => by rw [h, map_zero] at hv; exact zero_ne_one hv
    have hi : (T : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
    have e1 : (1 : E) ⊗ₜ[F] (T : v.adicCompletion F)⁻¹ * inclE (F := F) (v.adicCompletion F) (T : E) = 1 := by
      rw [map_natCast, ← map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := v.adicCompletion F))]
      show (1 : E) ⊗ₜ[F] _ * (1 : E) ⊗ₜ[F] _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ h0]
      rfl
    have e : y = ∑ j, (⟨_, mul_mem (hy j) (one_tmul_mem (E := E) v hi)⟩ : intV E v) •
        fun i => inclE (F := F) (v.adicCompletion F) ((Pi.single j (T : E) : Fin n → E) i) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · show _ = y i * _ * inclE (F := F) (v.adicCompletion F) ((Pi.single i (T : E) : Fin n → E) i)
        rw [Pi.single_eq_same, mul_assoc, e1, mul_one]
      · intro j _ hj
        show y j * _ * inclE (F := F) (v.adicCompletion F) ((Pi.single j (T : E) : Fin n → E) i) = 0
        rw [Pi.single_eq_of_ne hj.symm, map_zero, mul_zero]
      · exact fun h => absurd (Finset.mem_univ i) h
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h2 j, rfl⟩)

/- English proof (translation)
Establish `h` using `(hL _).1 ((hx.2 (Pi.single j 1)).1 ((hL _).2 fun b => by`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _])) i`. Simplify using `using h`.
-/
theorem entry_mem {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)} {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : ∀ y, y ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔ ∀ b, y b ∈ intV E v)
    {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hx : x ∈ levelVL σ J v L) (i j : Fin n) :
    (x : Matrix (Fin n) (Fin n) _) i j ∈ intV E v := by
  have h := (hL _).1 ((hx.2 (Pi.single j 1)).1 ((hL _).2 fun b => by
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _])) i
  simpa using h

section Phi

variable {v : HeightOneSpectrum (𝓞 F)} (φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
  (hφ : ∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = a)

/- English proof (translation)
Establish `h2 : IsIntegral (v.adicCompletionIntegers F) (φ (inclE (F` using `F) (v.adicCompletion F) (r : E))) := IsIntegral.map_of_comp_eq (Int.castRingHom _) (φ.comp (inclE (F := F) (v.adicCompletion F))) (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe r)`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h2`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem phi_int (r : 𝓞 E) : φ (inclE (F := F) (v.adicCompletion F) (r : E)) ∈ v.adicCompletionIntegers F := by
  have h2 : IsIntegral (v.adicCompletionIntegers F) (φ (inclE (F := F) (v.adicCompletion F) (r : E))) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) (φ.comp (inclE (F := F) (v.adicCompletion F))) (RingHom.ext_int _ _)
      (RingOfIntegers.isIntegral_coe r)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact y.2

include hφ in
/- English proof (translation)
Establish `h : intV E v ≤ (v.adicCompletionIntegers F).toSubring.comap φ`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨y, rfl⟩)`. Conclude with `phi_int φ x`. Use `show φ (1 ⊗ₜ[F] _) ∈ v.adicCompletionIntegers F`.

Rewrite using `[hφ]`. Conclude with `y.2`. Conclude with `h hy`.
-/
theorem phi_mem {y : E ⊗[F] v.adicCompletion F} (hy : y ∈ intV E v) : φ y ∈ v.adicCompletionIntegers F := by
  have h : intV E v ≤ (v.adicCompletionIntegers F).toSubring.comap φ := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨y, rfl⟩)
    · exact phi_int φ x
    · show φ (1 ⊗ₜ[F] _) ∈ v.adicCompletionIntegers F
      rw [hφ]
      exact y.2
  exact h hy

def resPhi : 𝓞 E →+* Formalism.L2.Forms.kv F v :=
  (IsLocalRing.residue (v.adicCompletionIntegers F)).comp
    (((φ.comp (inclE (F := F) (v.adicCompletion F))).comp (algebraMap (𝓞 E) E)).codRestrict
      (v.adicCompletionIntegers F).toSubring (phi_int φ))

/- English proof (translation)
Rewrite using `[IsLocalRing.residue_eq_zero_iff]`. Conclude with `Valuation.mem_maximalIdeal_iff _ _`.
-/
theorem residue_eq_zero_iff (a : v.adicCompletionIntegers F) :
    IsLocalRing.residue (v.adicCompletionIntegers F) a = 0 ↔ Valued.v (a : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff _ _

/- English proof (translation)
The claim follows from `residue_eq_zero_iff _`.
-/
theorem resPhi_eq_zero_iff (r : 𝓞 E) :
    resPhi φ r = 0 ↔ Valued.v (φ (inclE (F := F) (v.adicCompletion F) (r : E))) < 1 :=
  residue_eq_zero_iff _

include hφ in
/- English proof (translation)
Establish `e : inclE (F` using `F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) = (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) a := by show algebraMap F E a ⊗ₜ[F] 1 = _`. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]`. Rewrite using `[resPhi_eq_zero_iff, e, hφ, valued_algebraMap]`. Conclude with `HeightOneSpectrum.valuation_lt_one_iff_mem _ _`.
-/
theorem resPhi_algebraMap (a : 𝓞 F) : resPhi φ (algebraMap (𝓞 F) (𝓞 E) a) = 0 ↔ a ∈ v.asIdeal := by
  have e : inclE (F := F) (v.adicCompletion F) ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) =
      (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) a := by
    show algebraMap F E a ⊗ₜ[F] 1 = _
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  rw [resPhi_eq_zero_iff, e, hφ, valued_algebraMap]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem _ _

section Prime

variable {w : HeightOneSpectrum (𝓞 E)}
  (hw : ∀ r : 𝓞 E, r ∈ w.asIdeal ↔ Valued.v (φ (inclE (F := F) (v.adicCompletion F) (r : E))) < 1)

include hw in
/- English proof (translation)
Take `⟨r, d, e⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer w y hy.le`. Establish `hd : Valued.v (φ (inclE (F` using `F) (v.adicCompletion F) ((d : 𝓞 E) : E))) = 1 := le_antisymm (phi_int φ _) (not_lt.1 fun h => d.2 ((hw _).2 h))`. Establish `hr : r ∈ w.asIdeal`. Use `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w r).1 ?_` and prove the remaining obligations. Use `show w.valuation E (algebraMap (𝓞 E) E r) < 1`.

Rewrite using `[← e, map_mul, CharValCompare.val_of_notMem d.2, mul_one]`. Conclude with `hy`. Use `(hw r).1 hr` as an intermediate fact. Rewrite `this` using `[show (r : E) = y * ((d : 𝓞 E) : E) from e.symm, map_mul, map_mul, map_mul, hd, mul_one]`. Then use the resulting hypothesis.
-/
theorem phi_lt_of_lt {y : E} (hy : w.valuation E y < 1) : Valued.v (φ (inclE (F := F) (v.adicCompletion F) y)) < 1 := by
  obtain ⟨r, d, e⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer w y hy.le
  have hd : Valued.v (φ (inclE (F := F) (v.adicCompletion F) ((d : 𝓞 E) : E))) = 1 :=
    le_antisymm (phi_int φ _) (not_lt.1 fun h => d.2 ((hw _).2 h))
  have hr : r ∈ w.asIdeal := by
    refine (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w r).1 ?_
    show w.valuation E (algebraMap (𝓞 E) E r) < 1
    rw [← e, map_mul, CharValCompare.val_of_notMem d.2, mul_one]
    exact hy
  have := (hw r).1 hr
  rwa [show (r : E) = y * ((d : 𝓞 E) : E) from e.symm, map_mul, map_mul, map_mul, hd, mul_one] at this

include hφ hw in
/- English proof (translation)
Take `⟨y, N, r, hr, hN, e⟩` from `exists_approx_small z {w} (γ := 1) one_ne_zero`. Establish `hN'` using `hN w (Finset.mem_singleton_self w)`. Establish `h1 : w.valuation E y < 1`. Rewrite using `[← valued_algebraMap, ← adAt_inclE F, ← sub_eq_iff_eq_add.2 e, map_sub]`. Conclude with `Valuation.map_sub_lt _ hz (valued_nat_mul_lt hr hN')`.

Establish `h2 : Valued.v (N : v.adicCompletion F) < 1`. Rewrite `hN'` using `[valued_natCast]`. Use `phi_lt_of_lt φ hw hN'` as an intermediate fact. Rewrite `this` using `[map_natCast (algebraMap (𝓞 E) E), map_natCast (inclE (F := F) (v.adicCompletion F)), map_natCast φ]`. Then use the resulting hypothesis. Establish `h3 : Valued.v (φ (prV (E` using `E) v r)) ≤ 1 := phi_mem φ hφ (afsplit_prV_int v r hr)`.

Establish `e2 : φ (prV (E` using `E) v z) = φ (inclE (F := F) (v.adicCompletion F) y) + N * φ (prV (E := E) v r) := by`. Rewrite using `[e, map_add (prV (E := E) v), map_add φ, afsplit_prV_inclE, map_mul (prV (E := E) v), map_mul φ, map_natCast (prV (E := E) v), map_natCast φ]`. Rewrite using `[e2]`. Use `Valuation.map_add_lt _ (phi_lt_of_lt φ hw h1) ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_mul]`.

Conclude with `(mul_le_of_le_one_right' h3).trans_lt h2`.
-/
theorem phi_prV_lt {z : AfE F E} (hz : Valued.v (adAt F w z) < 1) : Valued.v (φ (prV (E := E) v z)) < 1 := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small z {w} (γ := 1) one_ne_zero
  have hN' := hN w (Finset.mem_singleton_self w)
  have h1 : w.valuation E y < 1 := by
    rw [← valued_algebraMap, ← adAt_inclE F, ← sub_eq_iff_eq_add.2 e, map_sub]
    exact Valuation.map_sub_lt _ hz (valued_nat_mul_lt hr hN')
  have h2 : Valued.v (N : v.adicCompletion F) < 1 := by
    rw [valued_natCast] at hN'
    have := phi_lt_of_lt φ hw hN'
    rwa [map_natCast (algebraMap (𝓞 E) E), map_natCast (inclE (F := F) (v.adicCompletion F)), map_natCast φ] at this
  have h3 : Valued.v (φ (prV (E := E) v r)) ≤ 1 := phi_mem φ hφ (afsplit_prV_int v r hr)
  have e2 : φ (prV (E := E) v z) = φ (inclE (F := F) (v.adicCompletion F) y) + N * φ (prV (E := E) v r) := by
    rw [e, map_add (prV (E := E) v), map_add φ, afsplit_prV_inclE, map_mul (prV (E := E) v), map_mul φ,
      map_natCast (prV (E := E) v), map_natCast φ]
  rw [e2]
  refine Valuation.map_add_lt _ (phi_lt_of_lt φ hw h1) ?_
  rw [Valuation.map_mul]
  exact (mul_le_of_le_one_right' h3).trans_lt h2

include hφ hw in
/- English proof (translation)
Rewrite `hr` using `[← adAt_inclE F, ← map_sub]`. Establish `h1` using `phi_prV_lt φ hφ hw hr`. Rewrite `h1` using `[map_sub (prV (E := E) v), map_sub φ, afsplit_prV_inclE]`. Establish `h2 : φ (prV (E` using `E) v z) ∈ v.adicCompletionIntegers F := by`. Establish `h3 : φ (prV (E` using `E) v z) - φ (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E r)) ∈ v.adicCompletionIntegers F := h1.le`.

Use `add_mem h3 (phi_int φ r)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Use `⟨h2, ?_⟩` and prove the remaining obligations. Establish `e : resPhi φ r = IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, phi_int φ r⟩` using `rfl`. Rewrite using `[e, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`.

Conclude with `h1`.
-/
theorem residue_phi {z : AfE F E} {r : 𝓞 E}
    (hr : Valued.v (adAt F w z - algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E r)) < 1) :
    ∃ h : φ (prV (E := E) v z) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, h⟩ = resPhi φ r := by
  rw [← adAt_inclE F, ← map_sub] at hr
  have h1 := phi_prV_lt φ hφ hw hr
  rw [map_sub (prV (E := E) v), map_sub φ, afsplit_prV_inclE] at h1
  have h2 : φ (prV (E := E) v z) ∈ v.adicCompletionIntegers F := by
    have h3 : φ (prV (E := E) v z) - φ (inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E r)) ∈
      v.adicCompletionIntegers F := h1.le
    have := add_mem h3 (phi_int φ r)
    rwa [sub_add_cancel] at this
  refine ⟨h2, ?_⟩
  have e : resPhi φ r = IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, phi_int φ r⟩ := rfl
  rw [e, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact h1

end Prime

include hφ in

/- English proof (translation)
Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Take `⟨w, hw0⟩ : ∃ w : HeightOneSpectrum (𝓞 E), ∀ r, r ∈ w.asIdeal ↔ resPhi φ r = 0` from `⟨⟨RingHom.ker (resPhi φ), RingHom.ker_isPrime _, fun h => by`. Establish `h1 : algebraMap (𝓞 F) (𝓞 E) a ∈ RingHom.ker (resPhi φ)` using `(resPhi_algebraMap φ hφ a).2 ha`. Rewrite `h1` using `[h, Ideal.mem_bot]`. Conclude with `ha0 (by simpa using h1)⟩, fun _ => Iff.rfl⟩`.

Establish `hw` using `fun r => (hw0 r).trans (resPhi_eq_zero_iff φ r)`. Establish `hu : w.under (𝓞 F) = v` using `HeightOneSpectrum.ext (Ideal.ext fun a => (hw0 _).trans (resPhi_algebraMap φ hφ a))`. Use `⟨w, Ideal.Quotient.lift _ (resPhi φ) fun r hr => (hw0 r).1 hr, hu, hw, ?_⟩` and prove the remaining obligations. Introduce and unpack `z _ ⟨r, rfl, hr⟩`. Rewrite using `[Ideal.Quotient.lift_mk]`.

Conclude with `residue_phi φ hφ hw hr`.
-/
theorem exists_prime : ∃ (w : HeightOneSpectrum (𝓞 E)) (ρ : 𝓞 E ⧸ w.asIdeal →+* Formalism.L2.Forms.kv F v), w.under (𝓞 F) = v ∧
    (∀ r : 𝓞 E, r ∈ w.asIdeal ↔ Valued.v (φ (inclE (F := F) (v.adicCompletion F) (r : E))) < 1) ∧
    ∀ (z : AfE F E) (c : 𝓞 E ⧸ w.asIdeal), HasRes w (adAt F w z) c →
      ∃ h : φ (prV (E := E) v z) ∈ v.adicCompletionIntegers F, IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, h⟩ = ρ c := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  obtain ⟨w, hw0⟩ : ∃ w : HeightOneSpectrum (𝓞 E), ∀ r, r ∈ w.asIdeal ↔ resPhi φ r = 0 :=
    ⟨⟨RingHom.ker (resPhi φ), RingHom.ker_isPrime _, fun h => by
      have h1 : algebraMap (𝓞 F) (𝓞 E) a ∈ RingHom.ker (resPhi φ) := (resPhi_algebraMap φ hφ a).2 ha
      rw [h, Ideal.mem_bot] at h1
      exact ha0 (by simpa using h1)⟩, fun _ => Iff.rfl⟩
  have hw := fun r => (hw0 r).trans (resPhi_eq_zero_iff φ r)
  have hu : w.under (𝓞 F) = v := HeightOneSpectrum.ext (Ideal.ext fun a => (hw0 _).trans (resPhi_algebraMap φ hφ a))
  refine ⟨w, Ideal.Quotient.lift _ (resPhi φ) fun r hr => (hw0 r).1 hr, hu, hw, ?_⟩
  rintro z _ ⟨r, rfl, hr⟩
  rw [Ideal.Quotient.lift_mk]
  exact residue_phi φ hφ hw hr

end Phi

end Places

section Res

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Take `⟨r, -, hr⟩` from `h`. Rewrite using `[← sub_add_cancel z (algebraMap E _ (algebraMap (𝓞 E) E r))]`. Use `Valuation.map_add_le _ hr.le ?_` and prove the remaining obligations. Rewrite using `[valued_algebraMap]`. Conclude with `HeightOneSpectrum.valuation_le_one (K := E) P r`.
-/
theorem hasRes_le {z : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal} (h : HasRes P z c) : Valued.v z ≤ 1 := by
  obtain ⟨r, -, hr⟩ := h
  rw [← sub_add_cancel z (algebraMap E _ (algebraMap (𝓞 E) E r))]
  refine Valuation.map_add_le _ hr.le ?_
  rw [valued_algebraMap]
  exact HeightOneSpectrum.valuation_le_one (K := E) P r

/- English proof (translation)
Simplify using `using hasRes_coe P 0`.
-/
theorem hasRes_zero : HasRes P 0 0 := by simpa using hasRes_coe P 0

/- English proof (translation)
Simplify using `using hasRes_coe P 1`.
-/
theorem hasRes_one : HasRes P 1 1 := by simpa using hasRes_coe P 1

/- English proof (translation)
Take `⟨r, rfl, hr⟩` from `h`. Take `⟨r', rfl, hr'⟩` from `h'`. Use `⟨r + r', map_add _ _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, add_sub_add_comm]`. Conclude with `Valuation.map_add_lt _ hr hr'`.
-/
theorem hasRes_add {z z' : P.adicCompletion E} {c c' : 𝓞 E ⧸ P.asIdeal} (h : HasRes P z c) (h' : HasRes P z' c') :
    HasRes P (z + z') (c + c') := by
  obtain ⟨r, rfl, hr⟩ := h
  obtain ⟨r', rfl, hr'⟩ := h'
  refine ⟨r + r', map_add _ _ _, ?_⟩
  rw [map_add, map_add, add_sub_add_comm]
  exact Valuation.map_add_lt _ hr hr'

/- English proof (translation)
Establish `h0` using `hasRes_le h`. Take `⟨r, rfl, hr⟩` from `h`. Take `⟨r', rfl, hr'⟩` from `h'`. Establish `h1` using `hasRes_le (hasRes_coe P r')`. Use `⟨r * r', map_mul _ _ _, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul]`. Establish `e : ∀ a b a' b' : P.adicCompletion E, a * b - a' * b' = a * (b - b') + (a - a') * b'` using `fun _ _ _ _ => by ring`. Rewrite using `[e]`. Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `(mul_le_of_le_one_left' h0).trans_lt hr'`. Rewrite using `[map_mul]`. Conclude with `(mul_le_of_le_one_right' h1).trans_lt hr`.
-/
theorem hasRes_mul {z z' : P.adicCompletion E} {c c' : 𝓞 E ⧸ P.asIdeal} (h : HasRes P z c) (h' : HasRes P z' c') :
    HasRes P (z * z') (c * c') := by
  have h0 := hasRes_le h
  obtain ⟨r, rfl, hr⟩ := h
  obtain ⟨r', rfl, hr'⟩ := h'
  have h1 := hasRes_le (hasRes_coe P r')
  refine ⟨r * r', map_mul _ _ _, ?_⟩
  rw [map_mul, map_mul]
  have e : ∀ a b a' b' : P.adicCompletion E, a * b - a' * b' = a * (b - b') + (a - a') * b' := fun _ _ _ _ => by ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul]
    exact (mul_le_of_le_one_left' h0).trans_lt hr'
  · rw [map_mul]
    exact (mul_le_of_le_one_right' h1).trans_lt hr

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hasRes_zero`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `hasRes_add (h a) ih`.
-/
theorem hasRes_sum {ι : Type} (s : Finset ι) {z : ι → P.adicCompletion E} {c : ι → 𝓞 E ⧸ P.asIdeal}
    (h : ∀ i, HasRes P (z i) (c i)) : HasRes P (∑ i ∈ s, z i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasRes_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact hasRes_add (h a) ih

variable {F : Type} [Field F] [NumberField F] [Algebra F E] {n : ℕ}

/- English proof (translation)
Take `⟨y, N, r, hr, hN, e⟩` from `exists_approx_small z {P} (γ := 1) one_ne_zero`. Establish `h0` using `valued_nat_mul_lt hr (hN P (by simp))`. Establish `h1 : P.valuation E y ≤ 1`. Rewrite using `[← valued_algebraMap, ← adAt_inclE F, ← sub_eq_iff_eq_add.2 e, map_sub]`. Conclude with `Valuation.map_sub_le _ h h0.le`.

Take `⟨a, ha⟩` from `HeightOneSpectrum.exists_valuation_sub_lt_of_integer P h1 1`. Use `⟨_, a, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[e, map_add, adAt_inclE, add_sub_right_comm, ← map_sub]`. Use `Valuation.map_add_lt _ ?_ h0` and prove the remaining obligations. Rewrite using `[valued_algebraMap, Valuation.map_sub_swap]`.

Simplify using `using ha`.
-/
theorem exists_hasRes {z : AfE F E} (h : Valued.v (adAt F P z) ≤ 1) : ∃ c, HasRes P (adAt F P z) c := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small z {P} (γ := 1) one_ne_zero
  have h0 := valued_nat_mul_lt hr (hN P (by simp))
  have h1 : P.valuation E y ≤ 1 := by
    rw [← valued_algebraMap, ← adAt_inclE F, ← sub_eq_iff_eq_add.2 e, map_sub]
    exact Valuation.map_sub_le _ h h0.le
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer P h1 1
  refine ⟨_, a, rfl, ?_⟩
  rw [e, map_add, adAt_inclE, add_sub_right_comm, ← map_sub]
  refine Valuation.map_add_lt _ ?_ h0
  rw [valued_algebraMap, Valuation.map_sub_swap]
  simpa using ha

def IsRed (P : HeightOneSpectrum (𝓞 E)) (x : GL (Fin n) (AfE F E)) (A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) : Prop :=
  ∀ i j, HasRes P (adAt F P ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j)) (A i j)

/- English proof (translation)
Introduce `i j` and use `by rw [Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum] exact hasRes_sum _ fun l => by rw [map_mul]; exact hasRes_mul (h i l) (h' l j)`.
-/
theorem IsRed.mul {x y : GL (Fin n) (AfE F E)} {A B : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)} (h : IsRed P x A)
    (h' : IsRed P y B) : IsRed P (x * y) (A * B) := fun i j => by
  rw [Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum]
  exact hasRes_sum _ fun l => by rw [map_mul]; exact hasRes_mul (h i l) (h' l j)

/- English proof (translation)
The claim follows from `Matrix.ext fun i j => (h i j).unique (h' i j)`.
-/
theorem IsRed.unique {x : GL (Fin n) (AfE F E)} {A B : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)} (h : IsRed P x A)
    (h' : IsRed P x B) : A = B := Matrix.ext fun i j => (h i j).unique (h' i j)

/- English proof (translation)
Introduce `i j` and use `by rw [Units.val_one, Matrix.one_apply, Matrix.one_apply] split_ifs · rw [map_one]; exact hasRes_one · rw [map_zero]; exact hasRes_zero`.
-/
theorem isRed_one : IsRed P (1 : GL (Fin n) (AfE F E)) 1 := fun i j => by
  rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [map_one]; exact hasRes_one
  · rw [map_zero]; exact hasRes_zero

/- English proof (translation)
Introduce `i j` and use `bc_adAt_congr hP e i j ▸ h i j`.
-/
theorem IsRed.congr {v : HeightOneSpectrum (𝓞 F)} (hP : P.under (𝓞 F) = v) {x y : GL (Fin n) (AfE F E)}
    (e : bc (prV (E := E) v) x = bc (prV (E := E) v) y) {A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)} (h : IsRed P x A) :
    IsRed P y A := fun i j => bc_adAt_congr hP e i j ▸ h i j

/- English proof (translation)
Use `choose A hA using fun i j => exists_hasRes (h i j)`. Use `choose B hB using fun i j => exists_hasRes (h' i j)`. Establish `h1 : IsRed P x (Matrix.of A)` using `hA`. Establish `h2 : IsRed P x⁻¹ (Matrix.of B)` using `hB`. Establish `h3` using `h1.mul h2`.

Rewrite `h3` using `[mul_inv_cancel]`. Establish `h4` using `h3.unique isRed_one`. Conclude with `⟨⟨_, _, h4, mul_eq_one_comm.1 h4⟩, h1⟩`.
-/
theorem exists_isRed {x : GL (Fin n) (AfE F E)}
    (h : ∀ i j, Valued.v (adAt F P ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1)
    (h' : ∀ i j, Valued.v (adAt F P (((x⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1) :
    ∃ A : GL (Fin n) (𝓞 E ⧸ P.asIdeal), IsRed P x A := by
  choose A hA using fun i j => exists_hasRes (h i j)
  choose B hB using fun i j => exists_hasRes (h' i j)
  have h1 : IsRed P x (Matrix.of A) := hA
  have h2 : IsRed P x⁻¹ (Matrix.of B) := hB
  have h3 := h1.mul h2
  rw [mul_inv_cancel] at h3
  have h4 := h3.unique isRed_one
  exact ⟨⟨_, _, h4, mul_eq_one_comm.1 h4⟩, h1⟩

/- English proof (translation)
Unfold `Col2.pullV`. Rewrite using `[_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]`. Both sides reduce to the same expression.
-/
theorem pullV_mul (g m : GL (Fin n) (AfE F E)) [StarRing E] (x : Sp E n) (i : Fin n) :
    Col2.pullV (g * m⁻¹) x i = ∑ j, (m : Matrix (Fin n) (Fin n) (AfE F E)) i j * Col2.pullV g x j := by
  unfold Col2.pullV
  rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
  rfl

/- English proof (translation)
Rewrite using `[pullV_mul, map_sum]`. Conclude with `hasRes_sum _ fun l => by rw [map_mul]; exact hasRes_mul (hm i l) (h l)`.
-/
theorem hasRes_pullV [StarRing E] {g m : GL (Fin n) (AfE F E)} {A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)} (hm : IsRed P m A)
    {x : Sp E n} {c : Fin n → 𝓞 E ⧸ P.asIdeal} (h : ∀ i, HasRes P (adAt F P (Col2.pullV g x i)) (c i)) (i : Fin n) :
    HasRes P (adAt F P (Col2.pullV (g * m⁻¹) x i)) ((A *ᵥ c) i) := by
  rw [pullV_mul, map_sum]
  exact hasRes_sum _ fun l => by rw [map_mul]; exact hasRes_mul (hm i l) (h l)

end Res

section Pts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {hc : CMData F E} {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

/- English proof (translation)
The claim follows from `Submodule.map_id _`.
-/
theorem smul_N (p : DecoF E n ST SG Q) (h : GLG E n SG) (c : GLQ E n Q) :
    (((1, h, c) : UF E n × GLG E n SG × GLQ E n Q) • p).deco.1.N = p.deco.1.N := Submodule.map_id _

/- English proof (translation)
Use `⟨⟨(⟨_, decorated_lattice_exists hc n ST SG g hg⟩, fun P => absurd P.2 (hQ _)), fun P => absurd P.2 (hQ _)⟩, hg, PtExist.carries_globLat g, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P => absurd P.2 (hQ _)⟩` and prove the remaining obligations. Establish `e : lastIdx n = i` using `Fin.ext (by simp [lastIdx]; omega) replace hv : v ∈ Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) := hv show HasRes _ _ ((decoRaw ST SG g).f P v)`. Simplify using `only [decoRaw]`. Rewrite using `[if_pos (le_locP _ _ hv), e]`. Conclude with `PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)`.

Use `replace hv : v ∈ Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) := hv show HasRes _ _ ((decoRaw ST SG g).be P v i)`. Simplify using `only [decoRaw]`. Rewrite using `[if_pos (le_locP _ _ hv)]`. Conclude with `PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)`.
-/
theorem exists_pt [NeZero n] (hQ : ∀ P, P ∉ Q) {g : GL (Fin n) (AfE F E)} (hg : g ∈ Formalism.L2.Herm.UstdAf hc n) :
    ∃ q : DecoF E n ST SG Q, IsPtOf hc g q := by
  classical
  refine ⟨⟨(⟨_, decorated_lattice_exists hc n ST SG g hg⟩, fun P => absurd P.2 (hQ _)), fun P => absurd P.2 (hQ _)⟩, hg,
    PtExist.carries_globLat g, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P => absurd P.2 (hQ _)⟩
  · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    replace hv : v ∈ Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) := hv
    show HasRes _ _ ((decoRaw ST SG g).f P v)
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv), e]
    exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
  · replace hv : v ∈ Formalism.UG.CS.globLat g (Formalism.L2.Col.stdLat E n) := hv
    show HasRes _ _ ((decoRaw ST SG g).be P v i)
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv)]
    exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)

/- English proof (translation)
Use `⟨mul_mem hg.uni (inv_mem hm), fun z => ?_, fun P v hv i hi => ?_, fun w v hv i => ?_, fun P => absurd P.2 (hQ _)⟩` and prove the remaining obligations. Rewrite using `[smul_N]`. Use `(hg.lat z).trans ((mem_latS_std _).trans (Iff.trans ⟨fun h i => ?_, fun h i => ?_⟩ (mem_latS_std _).symm))` and prove the remaining obligations. Use `PtExist.mulVec_int h1 h i` as an intermediate fact. Rewrite using `[_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]` and apply the resulting hypothesis.

Use `PtExist.mulVec_int h2 h i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_left]`. Then use the resulting hypothesis. Rewrite `hv` using `[smul_N]`. Establish `e : adAt F P.1 (Col2.pullV (g * m⁻¹) v i) = adAt F P.1 (Col2.pullV (g * 1⁻¹) v i)`. Rewrite using `[pullV_mul, pullV_mul, map_sum, map_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by rw [map_mul, map_mul, hT _ P.2]`. Rewrite using `[e, inv_one, mul_one]`. Conclude with `hg.f P v hv i hi`. Rewrite `hv` using `[smul_N]`. Conclude with `hasRes_pullV (hh w) (hg.be w v hv) i`.
-/
theorem isPtOf_mul (hQ : ∀ P, P ∉ Q) {g m : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (hg : IsPtOf hc g p)
    (hm : m ∈ Formalism.L2.Herm.UstdAf hc n) (h1 : ∀ i j, (m : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E)
    (h2 : ∀ i j, ((m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E)
    (hT : ∀ P ∈ ST, ∀ i j, adAt F P ((m : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      adAt F P (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j))
    {h : GLG E n SG} (hh : ∀ w : SG, IsRed w.1 m (h w)) (c : GLQ E n Q) :
    IsPtOf hc (g * m⁻¹) (((1, h, c) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  refine ⟨mul_mem hg.uni (inv_mem hm), fun z => ?_, fun P v hv i hi => ?_, fun w v hv i => ?_, fun P => absurd P.2 (hQ _)⟩
  · rw [smul_N]
    refine (hg.lat z).trans ((mem_latS_std _).trans (Iff.trans ⟨fun h i => ?_, fun h i => ?_⟩ (mem_latS_std _).symm))
    · have := PtExist.mulVec_int h1 h i
      rwa [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
    · have := PtExist.mulVec_int h2 h i
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_left] at this
  · rw [smul_N] at hv
    have e : adAt F P.1 (Col2.pullV (g * m⁻¹) v i) = adAt F P.1 (Col2.pullV (g * 1⁻¹) v i) := by
      rw [pullV_mul, pullV_mul, map_sum, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, map_mul, hT _ P.2]
    rw [e, inv_one, mul_one]
    exact hg.f P v hv i hi
  · rw [smul_N] at hv
    exact hasRes_pullV (hh w) (hg.be w v hv) i

/- English proof (translation)
Use `Matrix.ext_of_mulVec_single fun j => ?_` and prove the remaining obligations. Take `⟨v, hv, e⟩` from `p.deco.2.be_surj w (Pi.single j 1)`. Rewrite using `[← e]`. Conclude with `h v hv`.
-/
theorem eq_of_be (p : DecoF E n ST SG Q) (w : SG) {A B : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)}
    (h : ∀ v ∈ p.deco.1.N, A *ᵥ p.deco.1.be w v = B *ᵥ p.deco.1.be w v) : A = B := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  obtain ⟨v, hv, e⟩ := p.deco.2.be_surj w (Pi.single j 1)
  rw [← e]
  exact h v hv

/- English proof (translation)
The claim follows from `funext fun w => Units.ext (eq_of_be p w fun v _ => congrArg (fun q : DecoF E n ST SG Q => q.deco.1.be w v) e)`.
-/
theorem eq_of_smul_eq (p : DecoF E n ST SG Q) {h h' : GLG E n SG} {c c' : GLQ E n Q}
    (e : ((1, h, c) : UF E n × GLG E n SG × GLQ E n Q) • p = ((1, h', c') : UF E n × GLG E n SG × GLQ E n Q) • p) : h = h' :=
  funext fun w => Units.ext (eq_of_be p w fun v _ => congrArg (fun q : DecoF E n ST SG Q => q.deco.1.be w v) e)

/- English proof (translation)
The claim follows from `eq_of_be p w fun v hv => funext fun i => (hasRes_pullV hA (hg.be w v hv) i).unique (hq.be w v ((smul_N p h c).symm ▸ hv) i)`.
-/
theorem eq_red {g m : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (hg : IsPtOf hc g p) {h : GLG E n SG} {c : GLQ E n Q}
    (hq : IsPtOf hc (g * m⁻¹) (((1, h, c) : UF E n × GLG E n SG × GLQ E n Q) • p)) (w : SG)
    {A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)} (hA : IsRed w.1 m A) : A = h w :=
  eq_of_be p w fun v hv => funext fun i =>
    (hasRes_pullV hA (hg.be w v hv) i).unique (hq.be w v ((smul_N p h c).symm ▸ hv) i)

end Pts

end GlobalTheory.Mem.Col2.LevRead
