import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFacts
open GlobalTheory.UnitLemma Polynomial Matrix

noncomputable section
namespace GlobalTheory.InertUnitOrb.ModelOfN

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]`.
-/
theorem sigma_smul {K : UQ} (B : InvAlg K) (e : K.E) (y : B.A) : B.σ (e • y) = K.c e • B.σ y := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]

/- English proof (translation)
Set `b` to `Module.finBasis K.E B.A`. Establish `hsp : ∀ y : B.A, B.σ y = ∑ j, K.c (b.repr y j) • B.σ (b j)`. Introduce `y`. Use `conv_lhs => rw [← b.sum_repr y]`. Rewrite using `[map_sum]`.

Simplify using `only [sigma_smul]`. Establish `li : LinearIndependent K.E (fun i => B.σ (b i))`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `h1` using `congrArg B.σ hg`.

Rewrite `h1` using `[map_sum, map_zero]`. Simplify using `only [sigma_smul, B.σ_σ] at h1`. Establish `h2` using `Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => K.c (g j)) h1 i`. Simplify using `using h2`. Establish `sp : ⊤ ≤ Submodule.span K.E (Set.range fun i => B.σ (b i))`.

Introduce `y _`. Establish `e` using `hsp (B.σ y)`. Rewrite `e` using `[B.σ_σ]`. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.

Set `b'` to `Module.Basis.mk li sp`. Establish `hb' : ∀ i, b' i = B.σ (b i)` using `fun i => Module.Basis.mk_apply li sp i`. Establish `hrep : ∀ y i, b'.repr (B.σ y) i = K.c (b.repr y i)`. Introduce `y i`. Rewrite using `[hsp y]`.

Simplify using `only [← hb']`. Rewrite using `[b'.repr_sum_self]`. Rewrite using `[Algebra.trace_eq_matrix_trace b' (B.σ w), Algebra.trace_eq_matrix_trace b w]`. Simplify using `only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hb', ← map_mul, hrep]`.
-/
theorem trace_sigma {K : UQ} (B : InvAlg K) (w : B.A) :
    Algebra.trace K.E B.A (B.σ w) = K.c (Algebra.trace K.E B.A w) := by
  classical
  let b := Module.finBasis K.E B.A
  have hsp : ∀ y : B.A, B.σ y = ∑ j, K.c (b.repr y j) • B.σ (b j) := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp only [sigma_smul]
  have li : LinearIndependent K.E (fun i => B.σ (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg B.σ hg
    rw [map_sum, map_zero] at h1
    simp only [sigma_smul, B.σ_σ] at h1
    have h2 := Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => K.c (g j)) h1 i
    simpa using h2
  have sp : ⊤ ≤ Submodule.span K.E (Set.range fun i => B.σ (b i)) := by
    intro y _
    have e := hsp (B.σ y)
    rw [B.σ_σ] at e
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let b' := Module.Basis.mk li sp
  have hb' : ∀ i, b' i = B.σ (b i) := fun i => Module.Basis.mk_apply li sp i
  have hrep : ∀ y i, b'.repr (B.σ y) i = K.c (b.repr y i) := by
    intro y i
    rw [hsp y]
    simp only [← hb']
    rw [b'.repr_sum_self]
  rw [Algebra.trace_eq_matrix_trace b' (B.σ w), Algebra.trace_eq_matrix_trace b w]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hb', ← map_mul, hrep]

section Abstract

variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]

/- English proof (translation)
Rewrite using `[hsym (a • z) y, hsmul, map_mul, ← hsym z y]`.
-/
theorem herm_smul_right (h : V → V → K.E)
    (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z) (hsym : ∀ y z, h z y = K.c (h y z))
    (a : K.E) (y z : V) : h y (a • z) = K.c a * h y z := by
  rw [hsym (a • z) y, hsmul, map_mul, ← hsym z y]

/- English proof (translation)
Rewrite using `[hsym (z + z') y, hadd, map_add, ← hsym, ← hsym]`.
-/
theorem herm_add_right (h : V → V → K.E) (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z)
    (hsym : ∀ y z, h z y = K.c (h y z)) (y z z' : V) : h y (z + z') = h y z + h y z' := by
  rw [hsym (z + z') y, hadd, map_add, ← hsym, ← hsym]

/- English proof (translation)
Rewrite using `[hadd, herm_add_right h hadd hsym, herm_add_right h hadd hsym, hsmul, hsmul, herm_smul_right h hsmul hsym, herm_smul_right h hsmul hsym]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_expand (h : V → V → K.E) (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z)
    (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z) (hsym : ∀ y z, h z y = K.c (h y z))
    (e : K.E) (y z : V) :
    h (e • y + z) (e • y + z) = e * K.c e * h y y + e * h y z + K.c e * h z y + h z z := by
  rw [hadd, herm_add_right h hadd hsym, herm_add_right h hadd hsym, hsmul, hsmul,
    herm_smul_right h hsmul hsym, herm_smul_right h hsmul hsym]
  ring

/- English proof (translation)
Take `⟨hN, -, ⟨ϖ, hϖ, -⟩, -⟩` from `UnramNorm.unram_quadratic_facts K`. Take `⟨θ, θ', hθ, hθm⟩` from `K.c_res`. Establish `hinj : Function.Injective (algebraMap K.O K.E)` using `IsFractionRing.injective _ _`. Use `set ι := algebraMap K.O K.E with hι`. Use `set m := IsLocalRing.maximalIdeal K.O with hm`.

Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `c1 : ∀ v ∈ L, ∃ a ∈ m, h v v = ι a`. Introduce `v hv`. Take `⟨a, ha⟩` from `(hdual v).1 hv v hv`.

Use `⟨a, ?_, ha.symm⟩` and prove the remaining obligations. Assume the negation of the conclusion as `ham`. Establish `hau : IsUnit a`. Assume the negation of the conclusion as `hnu`. Conclude with `ham ((IsLocalRing.mem_maximalIdeal _).2 hnu)`.

Establish `hfix : K.c (ι (hau.unit : K.O)) = ι (hau.unit : K.O)`. Simplify using `only [IsUnit.unit_spec]`. Rewrite using `[ha, ← hsym v v]`. Take `⟨z, hz⟩` from `hN hau.unit hfix`. Simplify using `only [IsUnit.unit_spec] at hz`.

Apply `hno (((z⁻¹ : K.Oˣ) : K.O) • v) (L.smul_mem _ hv)` to reduce the goal to its premises. Rewrite using `[← algebraMap_smul K.E (((z⁻¹ : K.Oˣ) : K.O)) v, hsmul, herm_smul_right h hsmul hsym, ← ha, hz]`. Establish `he : ι ((z⁻¹ : K.Oˣ) : K.O) * ι (z : K.O) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Establish `hce : K.c (ι ((z⁻¹ : K.Oˣ) : K.O)) * K.c (ι (z : K.O)) = 1`.

Rewrite using `[← map_mul, he, map_one]`. Take the linear combination `(K.c (ι ((z⁻¹ : K.Oˣ) : K.O)) * K.c (ι (z : K.O))) * he + hce`. Establish `c2 : ∀ y ∈ L, ∀ z ∈ L, ∃ a ∈ m, h y z = ι a`. Introduce `y hy z hz`. Take `⟨a, ha⟩` from `(hdual y).1 hy z hz`.

Use `⟨a, ?_, ha.symm⟩` and prove the remaining obligations. Establish `hzy : h z y = ι (UnramNorm.cO K a)` using `by rw [UnramNorm.cO_spec, ha, ← hsym]`. Take `⟨a2, ha2m, ha2⟩` from `c1 y hy`. Take `⟨a3, ha3m, ha3⟩` from `c1 z hz`. Take `⟨a1, ha1m, ha1⟩` from `c1 (θ • y + z) (L.add_mem (L.smul_mem θ hy) hz)`.

Take `⟨a4, ha4m, ha4⟩` from `c1 ((1 : K.O) • y + z) (L.add_mem (L.smul_mem 1 hy) hz)`. Rewrite `ha1` using `[← algebraMap_smul K.E θ y, herm_expand h hadd hsmul hsym, hθ, ha2, ha3, ← ha, hzy]`. Rewrite `ha4` using `[← algebraMap_smul K.E (1 : K.O) y, herm_expand h hadd hsmul hsym, ha2, ha3, ← ha, hzy, map_one, map_one]`. Establish `e1 : a1 = θ * θ' * a2 + θ * a + θ' * UnramNorm.cO K a + a3` using `hinj (by`. Rewrite using `[← ha1]`.

Simplify using `only [map_add, map_mul]`. Use the proof step `rfl)`. Establish `e4 : a4 = a2 + a + UnramNorm.cO K a + a3` using `hinj (by`. Rewrite using `[← ha4]`. Simplify using `only [map_add, map_mul]`.

Use the proof step `ring)`. Establish `hmem : (θ - θ') * a ∈ m`. Establish `: (θ - θ') * a = (a1 - θ * θ' * a2 - a3) - θ' * (a4 - a2 - a3)`. Rewrite using `[e1, e4]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Use `m.sub_mem (m.sub_mem (m.sub_mem ha1m (m.mul_mem_left _ ha2m)) ha3m) (m.mul_mem_left _ ?_)` and prove the remaining obligations. Conclude with `m.sub_mem (m.sub_mem ha4m ha2m) ha3m`. Break down `(IsLocalRing.maximalIdeal.isMaximal K.O).isPrime.mem_or_mem hmem with h1 | h1` into its components or cases. Conclude with `absurd h1 hθm`.

Conclude with `h1`. Establish `hϖ0 : ι ϖ ≠ 0` using `fun h0 => hϖ.ne_zero (hinj (by rw [h0, map_zero]))`. Establish `hmϖ : m = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Establish `c3 : L ≤ m • L`. Introduce `y hy`.

Establish `hy' : (ι ϖ)⁻¹ • y ∈ L`. Rewrite using `[hdual]`. Introduce `z hz`. Take `⟨a, ham, ha⟩` from `c2 y hy z hz`. Rewrite `ham` using `[hmϖ, Ideal.mem_span_singleton']`.

Take `⟨d, rfl⟩` from `ham`. Use `⟨d, ?_⟩` and prove the remaining obligations. Rewrite using `[hsmul, ha, map_mul]`. Clear the denominators using the available nonvanishing facts. Establish `: y = ϖ • ((ι ϖ)⁻¹ • y)`.

Rewrite using `[← algebraMap_smul K.E ϖ, smul_smul, mul_inv_cancel₀ hϖ0, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul (by rw [hmϖ]; exact Ideal.mem_span_singleton_self ϖ) hy'`. Establish `hL : L = ⊥` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m L hfg c3 (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)`. Establish `htop : (⊤ : Submodule K.E V) = ⊥` using `by rw [← hspan, hL]; simp`.

Use `haveI := Module.finrank_pos_iff.1 hpos`. Conclude with `bot_ne_top htop.symm`.
-/
theorem exists_unit_vector [FiniteDimensional K.E V] (h : V → V → K.E)
    (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z)
    (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z) (hsym : ∀ y z, h z y = K.c (h y z))
    (hpos : 0 < Module.finrank K.E V) (L : Submodule K.O V) (hfg : L.FG)
    (hspan : Submodule.span K.E (L : Set V) = ⊤)
    (hdual : ∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) :
    ∃ u ∈ L, h u u = 1 := by
  obtain ⟨hN, -, ⟨ϖ, hϖ, -⟩, -⟩ := UnramNorm.unram_quadratic_facts K
  obtain ⟨θ, θ', hθ, hθm⟩ := K.c_res
  have hinj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective _ _
  set ι := algebraMap K.O K.E with hι
  set m := IsLocalRing.maximalIdeal K.O with hm
  by_contra hno
  push_neg at hno
  have c1 : ∀ v ∈ L, ∃ a ∈ m, h v v = ι a := by
    intro v hv
    obtain ⟨a, ha⟩ := (hdual v).1 hv v hv
    refine ⟨a, ?_, ha.symm⟩
    by_contra ham
    have hau : IsUnit a := by
      by_contra hnu
      exact ham ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    have hfix : K.c (ι (hau.unit : K.O)) = ι (hau.unit : K.O) := by
      simp only [IsUnit.unit_spec]
      rw [ha, ← hsym v v]
    obtain ⟨z, hz⟩ := hN hau.unit hfix
    simp only [IsUnit.unit_spec] at hz
    apply hno (((z⁻¹ : K.Oˣ) : K.O) • v) (L.smul_mem _ hv)
    rw [← algebraMap_smul K.E (((z⁻¹ : K.Oˣ) : K.O)) v, hsmul, herm_smul_right h hsmul hsym, ← ha, hz]
    have he : ι ((z⁻¹ : K.Oˣ) : K.O) * ι (z : K.O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hce : K.c (ι ((z⁻¹ : K.Oˣ) : K.O)) * K.c (ι (z : K.O)) = 1 := by
      rw [← map_mul, he, map_one]
    linear_combination (K.c (ι ((z⁻¹ : K.Oˣ) : K.O)) * K.c (ι (z : K.O))) * he + hce
  have c2 : ∀ y ∈ L, ∀ z ∈ L, ∃ a ∈ m, h y z = ι a := by
    intro y hy z hz
    obtain ⟨a, ha⟩ := (hdual y).1 hy z hz
    refine ⟨a, ?_, ha.symm⟩
    have hzy : h z y = ι (UnramNorm.cO K a) := by rw [UnramNorm.cO_spec, ha, ← hsym]
    obtain ⟨a2, ha2m, ha2⟩ := c1 y hy
    obtain ⟨a3, ha3m, ha3⟩ := c1 z hz
    obtain ⟨a1, ha1m, ha1⟩ := c1 (θ • y + z) (L.add_mem (L.smul_mem θ hy) hz)
    obtain ⟨a4, ha4m, ha4⟩ := c1 ((1 : K.O) • y + z) (L.add_mem (L.smul_mem 1 hy) hz)
    rw [← algebraMap_smul K.E θ y, herm_expand h hadd hsmul hsym, hθ, ha2, ha3, ← ha, hzy] at ha1
    rw [← algebraMap_smul K.E (1 : K.O) y, herm_expand h hadd hsmul hsym, ha2, ha3, ← ha, hzy,
      map_one, map_one] at ha4
    have e1 : a1 = θ * θ' * a2 + θ * a + θ' * UnramNorm.cO K a + a3 := hinj (by
      rw [← ha1]; simp only [map_add, map_mul]; rfl)
    have e4 : a4 = a2 + a + UnramNorm.cO K a + a3 := hinj (by
      rw [← ha4]; simp only [map_add, map_mul]; ring)
    have hmem : (θ - θ') * a ∈ m := by
      have : (θ - θ') * a = (a1 - θ * θ' * a2 - a3) - θ' * (a4 - a2 - a3) := by
        rw [e1, e4]; ring
      rw [this]
      refine m.sub_mem (m.sub_mem (m.sub_mem ha1m (m.mul_mem_left _ ha2m)) ha3m) (m.mul_mem_left _ ?_)
      exact m.sub_mem (m.sub_mem ha4m ha2m) ha3m
    rcases (IsLocalRing.maximalIdeal.isMaximal K.O).isPrime.mem_or_mem hmem with h1 | h1
    · exact absurd h1 hθm
    · exact h1
  have hϖ0 : ι ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hinj (by rw [h0, map_zero]))
  have hmϖ : m = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have c3 : L ≤ m • L := by
    intro y hy
    have hy' : (ι ϖ)⁻¹ • y ∈ L := by
      rw [hdual]
      intro z hz
      obtain ⟨a, ham, ha⟩ := c2 y hy z hz
      rw [hmϖ, Ideal.mem_span_singleton'] at ham
      obtain ⟨d, rfl⟩ := ham
      refine ⟨d, ?_⟩
      rw [hsmul, ha, map_mul]
      field_simp
    have : y = ϖ • ((ι ϖ)⁻¹ • y) := by
      rw [← algebraMap_smul K.E ϖ, smul_smul, mul_inv_cancel₀ hϖ0, one_smul]
    rw [this]
    exact Submodule.smul_mem_smul (by rw [hmϖ]; exact Ideal.mem_span_singleton_self ϖ) hy'
  have hL : L = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m L hfg c3
    (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
  have htop : (⊤ : Submodule K.E V) = ⊥ := by rw [← hspan, hL]; simp
  haveI := Module.finrank_pos_iff.1 hpos
  exact bot_ne_top htop.symm

end Abstract

section Induction

variable {K : UQ}

/- English proof (translation)
Use `haveI := isNoetherian_of_fg_of_noetherian L hfg`. Establish `h1` using `(IsNoetherian.noetherian (N.comap L.subtype)).map L.subtype`. Rewrite `h1` using `[Submodule.map_comap_subtype, inf_eq_right.2 hle]`. Then use the resulting hypothesis.
-/
theorem fg_of_le {V : Type} [AddCommGroup V] [Module K.O V] (L N : Submodule K.O V) (hfg : L.FG) (hle : N ≤ L) :
    N.FG := by
  haveI := isNoetherian_of_fg_of_noetherian L hfg
  have h1 := (IsNoetherian.noetherian (N.comap L.subtype)).map L.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h1

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intros`. Conclude with `⟨Fin.elim0, fun i => Fin.elim0 i⟩`. Consider the case `succ n ih`. Introduce `V _ _ _ _ _ h hadd hsmul hsym hn L hfg hspan hdual`.

Take `⟨u, huL, huu⟩` from `exists_unit_vector h hadd hsmul hsym (by omega) L hfg hspan hdual`. Set `f : V →ₗ[K.E] K.E` to `{ toFun := fun y => h y u, map_add' := fun y y' => hadd y y' u, map_smul' := fun a y => hsmul a y u }`. Establish `hf : ∀ y, f y = h y u` using `fun y => rfl`. Set `W` to `LinearMap.ker f`. Establish `hmemW : ∀ y : V, y ∈ W ↔ h y u = 0` using `fun y => LinearMap.mem_ker`.

Establish `hrange : LinearMap.range f = ⊤`. Rewrite using `[LinearMap.range_eq_top]`. Introduce `a`. Conclude with `⟨a • u, by rw [hf, hsmul, huu, mul_one]⟩`. Establish `hfW : Module.finrank K.E W = n` using `by show Module.finrank K.E (LinearMap.ker f) = n`.

Use `LinearMap.finrank_range_add_finrank_ker f` as an intermediate fact. Rewrite `this` using `[hrange, finrank_top, Module.finrank_self, hn]`. Use linear arithmetic over natural numbers and integers. Set `p : V →ₗ[K.E] W` to `LinearMap.codRestrict W (LinearMap.id - LinearMap.smulRight f u) (by`. Introduce `y`.

Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub, map_smul, hf u, huu, smul_eq_mul, mul_one, sub_self])`. Establish `hp : ∀ y, (p y : V) = y - h y u • u` using `fun y => rfl`. Establish `hpL : ∀ y ∈ L, (p y : V) ∈ L`. Introduce `y hy`. Take `⟨a, ha⟩` from `(hdual y).1 hy u huL`.

Rewrite using `[hp, ← ha, algebraMap_smul]`. Conclude with `L.sub_mem hy (L.smul_mem a huL)`. Establish `hpW : ∀ w : W, p w = w`. Introduce `w`. Use `ext`.

Rewrite using `[hp, (hmemW w).1 w.2, zero_smul, sub_zero]`. Set `L' : Submodule K.O W` to `L.comap (W.subtype.restrictScalars K.O)`. Establish `hL' : ∀ y : W, y ∈ L' ↔ (y : V) ∈ L` using `fun y => Iff.rfl`. Establish `hfg' : L'.FG`. Use `Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars K.O) Subtype.val_injective ?_` and prove the remaining obligations.

Use `fg_of_le L _ hfg ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hy`. Establish `hspan' : Submodule.span K.E (L' : Set W) = ⊤`. Establish `hsurj : Function.Surjective p` using `fun w => ⟨(w : V), hpW w⟩`.

Establish `h1` using `Submodule.map_span p (L : Set V)`. Rewrite `h1` using `[hspan, Submodule.map_top, LinearMap.range_eq_top.2 hsurj]`. Rewrite using `[eq_top_iff, h1]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `(hL' _).2 (hpL y hy)`. Establish `hdual' : ∀ y : W, y ∈ L' ↔ ∀ z ∈ L', h (y : V) (z : V) ∈ (algebraMap K.O K.E).range`. Introduce `y`. Rewrite using `[hL', hdual]`. Prove the components needed by the constructor for the conclusion.

Introduce `H z hz`. Conclude with `H z ((hL' z).1 hz)`. Introduce `H z hz`. Establish `hz' : z = (p z : V) + h z u • u` using `by rw [hp]; abel`. Rewrite using `[hz', herm_add_right h hadd hsym, herm_smul_right h hsmul hsym, (hmemW y).1 y.2, mul_zero, add_zero]`.

Conclude with `H (p z) ((hL' _).2 (hpL z hz))`. Take `⟨w, hw⟩` from `ih W (fun y z => h y z) (fun y y' z => hadd y y' z) (fun a y z => hsmul a y z) (fun y z => hsym y z) hfW L' hfg' hspan' hdual'`. Use `⟨Fin.cons u (fun i => (w i : V)), ?_⟩` and prove the remaining obligations. Establish `hwu : ∀ i, h (w i : V) u = 0` using `fun i => (hmemW _).1 (w i).2`. Establish `huw : ∀ i, h u (w i : V) = 0` using `fun i => by rw [hsym, hwu, map_zero]`.

Introduce `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Simplify using `[huu]`. Simplify using `[huw, (Fin.succ_ne_zero j).symm]`. Simplify using `[hwu, Fin.succ_ne_zero i]`.

Simplify using `only [Fin.cons_succ, Fin.succ_inj]`. Conclude with `hw i j`.
-/
theorem exists_orthonormal (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (h : V → V → K.E),
    (∀ y y' z, h (y + y') z = h y z + h y' z) → (∀ (a : K.E) y z, h (a • y) z = a * h y z) →
    (∀ y z, h z y = K.c (h y z)) → Module.finrank K.E V = n → ∀ L : Submodule K.O V, L.FG →
    Submodule.span K.E (L : Set V) = ⊤ → (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∃ v : Fin n → V, ∀ i j, h (v i) (v j) = if i = j then 1 else 0 := by
  induction n with
  | zero => intros; exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro V _ _ _ _ _ h hadd hsmul hsym hn L hfg hspan hdual
    obtain ⟨u, huL, huu⟩ := exists_unit_vector h hadd hsmul hsym (by omega) L hfg hspan hdual
    let f : V →ₗ[K.E] K.E :=
      { toFun := fun y => h y u, map_add' := fun y y' => hadd y y' u, map_smul' := fun a y => hsmul a y u }
    have hf : ∀ y, f y = h y u := fun y => rfl
    let W := LinearMap.ker f
    have hmemW : ∀ y : V, y ∈ W ↔ h y u = 0 := fun y => LinearMap.mem_ker
    have hrange : LinearMap.range f = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro a
      exact ⟨a • u, by rw [hf, hsmul, huu, mul_one]⟩
    have hfW : Module.finrank K.E W = n := by
      show Module.finrank K.E (LinearMap.ker f) = n
      have := LinearMap.finrank_range_add_finrank_ker f
      rw [hrange, finrank_top, Module.finrank_self, hn] at this
      omega
    let p : V →ₗ[K.E] W := LinearMap.codRestrict W (LinearMap.id - LinearMap.smulRight f u) (by
      intro y
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub,
        map_smul, hf u, huu, smul_eq_mul, mul_one, sub_self])
    have hp : ∀ y, (p y : V) = y - h y u • u := fun y => rfl
    have hpL : ∀ y ∈ L, (p y : V) ∈ L := by
      intro y hy
      obtain ⟨a, ha⟩ := (hdual y).1 hy u huL
      rw [hp, ← ha, algebraMap_smul]
      exact L.sub_mem hy (L.smul_mem a huL)
    have hpW : ∀ w : W, p w = w := by
      intro w
      ext
      rw [hp, (hmemW w).1 w.2, zero_smul, sub_zero]
    let L' : Submodule K.O W := L.comap (W.subtype.restrictScalars K.O)
    have hL' : ∀ y : W, y ∈ L' ↔ (y : V) ∈ L := fun y => Iff.rfl
    have hfg' : L'.FG := by
      refine Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars K.O) Subtype.val_injective ?_
      refine fg_of_le L _ hfg ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    have hspan' : Submodule.span K.E (L' : Set W) = ⊤ := by
      have hsurj : Function.Surjective p := fun w => ⟨(w : V), hpW w⟩
      have h1 := Submodule.map_span p (L : Set V)
      rw [hspan, Submodule.map_top, LinearMap.range_eq_top.2 hsurj] at h1
      rw [eq_top_iff, h1]
      apply Submodule.span_mono
      rintro _ ⟨y, hy, rfl⟩
      exact (hL' _).2 (hpL y hy)
    have hdual' : ∀ y : W, y ∈ L' ↔ ∀ z ∈ L', h (y : V) (z : V) ∈ (algebraMap K.O K.E).range := by
      intro y
      rw [hL', hdual]
      constructor
      · intro H z hz
        exact H z ((hL' z).1 hz)
      · intro H z hz
        have hz' : z = (p z : V) + h z u • u := by rw [hp]; abel
        rw [hz', herm_add_right h hadd hsym, herm_smul_right h hsmul hsym, (hmemW y).1 y.2, mul_zero, add_zero]
        exact H (p z) ((hL' _).2 (hpL z hz))
    obtain ⟨w, hw⟩ := ih W (fun y z => h y z) (fun y y' z => hadd y y' z) (fun a y z => hsmul a y z)
      (fun y z => hsym y z) hfW L' hfg' hspan' hdual'
    refine ⟨Fin.cons u (fun i => (w i : V)), ?_⟩
    have hwu : ∀ i, h (w i : V) u = 0 := fun i => (hmemW _).1 (w i).2
    have huw : ∀ i, h u (w i : V) = 0 := fun i => by rw [hsym, hwu, map_zero]
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [huu]
    · simp [huw, (Fin.succ_ne_zero j).symm]
    · simp [hwu, Fin.succ_ne_zero i]
    · simp only [Fin.cons_succ, Fin.succ_inj]
      exact hw i j

end Induction

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `hN` to reduce the goal to its premises. Use `haveI : IsEmpty (Orb K.O B.T (B.X x)) := ⟨fun o => by`. Proceed by induction on `o using Quot.ind with`.

Consider the case `mk L => exact hne L.1 L.2⟩`. Unfold `InvAlg.N orbSum`. Conclude with `finsum_of_isEmpty _`.
-/
theorem exists_mem_X_of_N_ne_zero {K : UQ} (B : InvAlg K) (x : B.A) (hN : B.N x ≠ 0) : ∃ L, L ∈ B.X x := by
  by_contra hne
  push_neg at hne
  apply hN
  haveI : IsEmpty (Orb K.O B.T (B.X x)) := ⟨fun o => by
    induction o using Quot.ind with
    | mk L => exact hne L.1 L.2⟩
  unfold InvAlg.N orbSum
  exact finsum_of_isEmpty _

/- English proof (translation)
Set `ℓ : V → V →ₗ[K.E] K.E` to `fun z => { toFun := fun y => h y z, map_add' := fun y y' => hadd y y' z, map_smul' := fun a y => hsmul a y z }`. Establish `li : LinearIndependent K.E v`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `h1` using `congrArg (ℓ (v i)) hg`.

Rewrite `h1` using `[map_sum, map_zero]`. Simplify using `only [map_smul, smul_eq_mul] at h1`. Express the relevant statement in the definitionally equal form `∑ j, g j * h (v j) (v i) = 0 at h1`. Simplify `h1` using `[hv]`. Establish `sp : ⊤ ≤ Submodule.span K.E (Set.range v)`.

Conclude with `(Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card li, Fintype.card_fin, hn])).ge`. Conclude with `⟨Module.Basis.mk li sp, fun i => Module.Basis.mk_apply li sp i⟩`.
-/
theorem exists_basis_of_orthonormal {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [FiniteDimensional K.E V]
    (h : V → V → K.E) (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z)
    (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z) {n : ℕ} (hn : Module.finrank K.E V = n)
    (v : Fin n → V) (hv : ∀ i j, h (v i) (v j) = if i = j then 1 else 0) :
    ∃ b : Module.Basis (Fin n) K.E V, ∀ i, b i = v i := by
  let ℓ : V → V →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => h y z, map_add' := fun y y' => hadd y y' z, map_smul' := fun a y => hsmul a y z }
  have li : LinearIndependent K.E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg (ℓ (v i)) hg
    rw [map_sum, map_zero] at h1
    simp only [map_smul, smul_eq_mul] at h1
    change ∑ j, g j * h (v j) (v i) = 0 at h1
    simpa [hv] using h1
  have sp : ⊤ ≤ Submodule.span K.E (Set.range v) := by
    exact (Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card li, Fintype.card_fin, hn])).ge
  exact ⟨Module.Basis.mk li sp, fun i => Module.Basis.mk_apply li sp i⟩

/- English proof (translation)
Introduce `K B n x hn hσx hN`. Take `⟨L, ⟨hfg, hspan⟩, -, hdual⟩` from `exists_mem_X_of_N_ne_zero B (x : B.A) hN`. Establish `hadd : ∀ y y' z, B.herm x (y + y') z = B.herm x y z + B.herm x y' z`. Introduce `y y' z`. Simplify using `only [InvAlg.herm, mul_add, add_mul, map_add]`.

Establish `hsmul : ∀ (a : K.E) y z, B.herm x (a • y) z = a * B.herm x y z`. Introduce `a y z`. Simplify using `only [InvAlg.herm, mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]`. Establish `hsym : ∀ y z, B.herm x z y = K.c (B.herm x y z)`. Introduce `y z`.

Simplify using `only [InvAlg.herm]`. Rewrite using `[← trace_sigma B, map_mul B.σ, map_mul B.σ, B.σ_σ, hσx]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Take `⟨v, hv⟩` from `exists_orthonormal n B.A (B.herm x) hadd hsmul hsym hn L hfg hspan hdual`.

Take `⟨b, hb⟩` from `exists_basis_of_orthonormal (B.herm x) hadd hsmul hn v hv`. Set `ℓ : B.A → B.A →ₗ[K.E] K.E` to `fun z => { toFun := fun y => B.herm x y z, map_add' := fun y y' => hadd y y' z, map_smul' := fun a y => hsmul a y z }`. Establish `hexp : ∀ y w, B.herm x y w = ∑ i, b.repr y i * B.herm x (b i) w`. Introduce `y w`. Establish `h1 : ℓ w y = ℓ w (∑ i, b.repr y i • b i)` using `by rw [b.sum_repr]`.

Rewrite `h1` using `[map_sum]`. Simplify using `only [map_smul, smul_eq_mul] at h1`. Conclude with `h1`. Establish `hcol : ∀ i z, B.herm x (b i) z = K.c (b.repr z i)`. Introduce `i z`.

Rewrite using `[hsym, hexp z (b i)]`. Simplify using `only [hb, hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `⟨LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g), b.equivFun, hσx, fun y => ?_, fun y z => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]`. Both sides reduce to the same expression.

Rewrite using `[hexp y z]`. Simplify using `only [stdH, Module.Basis.equivFun_apply, hcol]`.
-/
theorem exists_model : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (x : B.Aˣ),
    Module.finrank K.E B.A = n → B.σ (x : B.A) = x → B.N x ≠ 0 →
    ∃ (γ : Matrix (Fin n) (Fin n) K.E) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by
  intro K B n x hn hσx hN
  obtain ⟨L, ⟨hfg, hspan⟩, -, hdual⟩ := exists_mem_X_of_N_ne_zero B (x : B.A) hN
  have hadd : ∀ y y' z, B.herm x (y + y') z = B.herm x y z + B.herm x y' z := by
    intro y y' z
    simp only [InvAlg.herm, mul_add, add_mul, map_add]
  have hsmul : ∀ (a : K.E) y z, B.herm x (a • y) z = a * B.herm x y z := by
    intro a y z
    simp only [InvAlg.herm, mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
  have hsym : ∀ y z, B.herm x z y = K.c (B.herm x y z) := by
    intro y z
    simp only [InvAlg.herm]
    rw [← trace_sigma B, map_mul B.σ, map_mul B.σ, B.σ_σ, hσx]
    congr 1
    ring
  obtain ⟨v, hv⟩ := exists_orthonormal n B.A (B.herm x) hadd hsmul hsym hn L hfg hspan hdual
  obtain ⟨b, hb⟩ := exists_basis_of_orthonormal (B.herm x) hadd hsmul hn v hv
  let ℓ : B.A → B.A →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => B.herm x y z, map_add' := fun y y' => hadd y y' z, map_smul' := fun a y => hsmul a y z }
  have hexp : ∀ y w, B.herm x y w = ∑ i, b.repr y i * B.herm x (b i) w := by
    intro y w
    have h1 : ℓ w y = ℓ w (∑ i, b.repr y i • b i) := by rw [b.sum_repr]
    rw [map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    exact h1
  have hcol : ∀ i z, B.herm x (b i) z = K.c (b.repr z i) := by
    intro i z
    rw [hsym, hexp z (b i)]
    simp only [hb, hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g), b.equivFun, hσx, fun y => ?_, fun y z => ?_⟩
  · rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
    rfl
  · rw [hexp y z]
    simp only [stdH, Module.Basis.equivFun_apply, hcol]

end GlobalTheory.InertUnitOrb.ModelOfN
