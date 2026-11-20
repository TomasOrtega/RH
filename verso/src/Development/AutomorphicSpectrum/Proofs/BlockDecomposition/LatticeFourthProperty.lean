import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open Polynomial

namespace GlobalTheory.CompanionTheory.UnitLattice

open PositivityTheory.Rg.Tf.Loc

variable {n : ℕ}

/- English proof (translation)
Establish `hinj : Function.Injective ((intO F).subtype)` using `Subtype.val_injective`. Set `A : Matrix (Fin n) (Fin n) (intO F)` to `fun i j => ⟨_, h1 i j⟩`. Set `B : Matrix (Fin n) (Fin n) (intO F)` to `fun i j => ⟨_, h2 i j⟩`. Establish `hA : A.map (intO F).subtype = (u : Matrix (Fin n) (Fin n) F)`. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `hB : B.map (intO F).subtype = ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hAB : A * B = 1`.

Apply `Matrix.map_injective hinj` to reduce the goal to its premises. Use `beta_reduce`. Rewrite using `[Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hBA : B * A = 1`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises.

Use `beta_reduce`. Rewrite using `[Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `⟨⟨A, B, hAB, hBA⟩, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hA`.
-/
theorem mem_unitGL_of_integral {F : Type*} [Field F] [ValuativeRel F] (u : GL (Fin n) F)
    (h1 : ∀ i j, (u : Matrix (Fin n) (Fin n) F) i j ∈ intO F)
    (h2 : ∀ i j, ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F) :
    u ∈ unitGL (n := Fin n) F := by
  have hinj : Function.Injective ((intO F).subtype) := Subtype.val_injective
  let A : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, h2 i j⟩
  have hA : A.map (intO F).subtype = (u : Matrix (Fin n) (Fin n) F) := by
    ext i j; rfl
  have hB : B.map (intO F).subtype = ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    ext i j; rfl
  have hAB : A * B = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBA : B * A = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hA

/- English proof (translation)
Take `⟨v, rfl⟩` from `hu`. Conclude with `((v : Matrix (Fin n) (Fin n) (intO F)) i j).2`.
-/
theorem integral_of_mem_unitGL {F : Type*} [Field F] [ValuativeRel F] {u : GL (Fin n) F}
    (hu : u ∈ unitGL (n := Fin n) F) (i j : Fin n) :
    (u : Matrix (Fin n) (Fin n) F) i j ∈ intO F := by
  obtain ⟨v, rfl⟩ := hu
  exact ((v : Matrix (Fin n) (Fin n) (intO F)) i j).2

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `i j`. Rewrite using `[pow_zero, Matrix.one_apply]`. Use `split_ifs`.

Conclude with `S.one_mem`. Conclude with `S.zero_mem`. Consider the case `succ m ih`. Introduce `i j`. Rewrite using `[pow_succ, Matrix.mul_apply]`.

Conclude with `S.sum_mem fun l _ => S.mul_mem (ih i l) (hM l j)`.
-/
theorem pow_entry_mem {F : Type*} [Field F] (S : Subring F) {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ i j, M i j ∈ S) (m : ℕ) : ∀ i j, (M ^ m) i j ∈ S := by
  induction m with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  | succ m ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact S.sum_mem fun l _ => S.mul_mem (ih i l) (hM l j)

/- English proof (translation)
Rewrite using `[aeval_eq_sum_range, Matrix.sum_apply]`. Use `S.sum_mem fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Conclude with `S.mul_mem (hp l) (pow_entry_mem S hM l i j)`.
-/
theorem aeval_entry_mem {F : Type*} [Field F] (S : Subring F) {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ i j, M i j ∈ S) {p : F[X]} (hp : ∀ i, p.coeff i ∈ S) (i j : Fin n) :
    (aeval M p) i j ∈ S := by
  rw [aeval_eq_sum_range, Matrix.sum_apply]
  refine S.sum_mem fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact S.mul_mem (hp l) (pow_entry_mem S hM l i j)

/- English proof (translation)
Rewrite using `[aeval_eq_sum_range, aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Units.conj_pow', mul_smul_comm, smul_mul_assoc]`.
-/
theorem conj_aeval {F : Type*} [Field F] (u : GL (Fin n) F) (M : Matrix (Fin n) (Fin n) F)
    (p : F[X]) :
    ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * aeval M p * (u : Matrix (Fin n) (Fin n) F) =
      aeval (((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * M * (u : Matrix (Fin n) (Fin n) F)) p := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Units.conj_pow', mul_smul_comm, smul_mul_assoc]

/- English proof (translation)
Establish `hent` using `integral_of_mem_unitGL hΓ`. Simplify using `only [Units.val_mul] at hent`. Apply `mem_unitGL_of_integral` to reduce the goal to its premises. Introduce `i j`. Simplify using `only [Units.val_mul]`.

Rewrite using `[hp, conj_aeval]`. Conclude with `aeval_entry_mem _ hent hpi i j`. Introduce `i j`. Establish `: (g⁻¹ * c * g)⁻¹ = g⁻¹ * c⁻¹ * g` using `by group`. Rewrite using `[this]`.

Simplify using `only [Units.val_mul]`. Rewrite using `[hq, conj_aeval]`. Conclude with `aeval_entry_mem _ hent hqi i j`.
-/
theorem conj_mem_unitGL {F : Type*} [Field F] [ValuativeRel F] {Γ c g : GL (Fin n) F} {p q : F[X]}
    (hp : (c : Matrix (Fin n) (Fin n) F) = aeval (Γ : Matrix (Fin n) (Fin n) F) p)
    (hpi : ∀ i, p.coeff i ∈ intO F)
    (hq : ((c⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = aeval (Γ : Matrix (Fin n) (Fin n) F) q)
    (hqi : ∀ i, q.coeff i ∈ intO F)
    (hΓ : g⁻¹ * Γ * g ∈ unitGL (n := Fin n) F) :
    g⁻¹ * c * g ∈ unitGL (n := Fin n) F := by
  have hent := integral_of_mem_unitGL hΓ
  simp only [Units.val_mul] at hent
  apply mem_unitGL_of_integral
  · intro i j
    simp only [Units.val_mul]
    rw [hp, conj_aeval]
    exact aeval_entry_mem _ hent hpi i j
  · intro i j
    have : (g⁻¹ * c * g)⁻¹ = g⁻¹ * c⁻¹ * g := by group
    rw [this]
    simp only [Units.val_mul]
    rw [hq, conj_aeval]
    exact aeval_entry_mem _ hent hqi i j

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `h1 : g⁻¹ * Γ * g = Γ` using `by rw [mul_assoc, ← hg]; group`. Establish `h2 : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (Γ : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) = Γ`. Use `congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) h1` as an intermediate fact. Simplify `this` using `only [Units.val_mul]`.

Simplify using `only [Units.val_mul]`. Rewrite using `[hp, conj_aeval, h2]`.
-/
theorem conj_eq_of_commute {F : Type*} [Field F] {Γ c g : GL (Fin n) F} {p : F[X]}
    (hp : (c : Matrix (Fin n) (Fin n) F) = aeval (Γ : Matrix (Fin n) (Fin n) F) p)
    (hg : g * Γ = Γ * g) : g⁻¹ * c * g = c := by
  apply Units.ext
  have h1 : g⁻¹ * Γ * g = Γ := by rw [mul_assoc, ← hg]; group
  have h2 : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (Γ : Matrix (Fin n) (Fin n) F) *
      (g : Matrix (Fin n) (Fin n) F) = Γ := by
    have := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) h1
    simpa only [Units.val_mul] using this
  simp only [Units.val_mul]
  rw [hp, conj_aeval, h2]

/- English proof (translation)
Establish `hpow : ∀ i : ℕ, (θ ^ i) u ∈ K`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simpa using hu`. Consider the case `succ i ih => rw [pow_succ_apply']`.

Conclude with `hK _ ih`. Proceed by induction on `m with`. Consider the case `zero => simpa using K.one_mem`. Consider the case `succ m ih => rw [twNorm_succ]`. Conclude with `K.mul_mem ih (hpow m)`.
-/
theorem twNorm_mem {G : Type*} [Group G] (θ : Monoid.End G) (K : Subgroup G)
    (hK : ∀ x ∈ K, θ x ∈ K) {u : G} (hu : u ∈ K) (m : ℕ) : twNorm θ m u ∈ K := by
  have hpow : ∀ i : ℕ, (θ ^ i) u ∈ K := by
    intro i
    induction i with
    | zero => simpa using hu
    | succ i ih => rw [pow_succ_apply']; exact hK _ ih
  induction m with
  | zero => simpa using K.one_mem
  | succ m ih => rw [twNorm_succ]; exact K.mul_mem ih (hpow m)

/- English proof (translation)
Establish `hfix : ∀ x : E, σ x = x → ∃ a : k, algebraMap k E a = x`. Introduce `x hx`. Establish `hσ : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) x`. Rewrite using `[MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`. Conclude with `hx`.

Establish `hall : ∀ τ : E ≃ₐ[k] E, τ x = x`. Introduce `τ`. Use `(Subgroup.zpowers_le.mpr hσ) (hgen τ)` as an intermediate fact. Rewrite `this` using `[MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`. Then use the resulting hypothesis. Use `(IsGalois.mem_bot_iff_fixed x).mpr hall` as an intermediate fact.

Rewrite `this` using `[IntermediateField.mem_bot]`. Then use the resulting hypothesis. Establish `hent : ∀ (h : GL (Fin n) E), sigmaGL σ h = h → ∀ i j, σ ((h : Matrix (Fin n) (Fin n) E) i j) = (h : Matrix (Fin n) (Fin n) E) i j`. Introduce `h hh i j`. Use `congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E) i j) hh` as an intermediate fact. Conclude with `this`.

Establish `hg' : sigmaGL σ g⁻¹ = g⁻¹` using `by rw [map_inv, hg]`. Use `choose A hA using fun i j => hfix _ (hent g hg i j)`. Use `choose B hB using fun i j => hfix _ (hent g⁻¹ hg' i j)`. Establish `hinj : Function.Injective (algebraMap k E)` using `(algebraMap k E).injective`. Establish `hAm : (Matrix.of A).map (algebraMap k E) = (g : Matrix (Fin n) (Fin n) E)`.

Use extensionality with `i j`. Conclude with `hA i j`. Establish `hBm : (Matrix.of B).map (algebraMap k E) = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)`. Use extensionality with `i j`. Conclude with `hB i j`.

Establish `hAB : Matrix.of A * Matrix.of B = 1`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises. Use `beta_reduce`. Rewrite using `[Matrix.map_mul, hAm, hBm, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hBA : Matrix.of B * Matrix.of A = 1`.

Apply `Matrix.map_injective hinj` to reduce the goal to its premises. Use `beta_reduce`. Rewrite using `[Matrix.map_mul, hAm, hBm, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Use `⟨⟨Matrix.of A, Matrix.of B, hAB, hBA⟩, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `hAm`.
-/
theorem exists_incl_of_fixed {k E : Type*} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) (g : GL (Fin n) E)
    (hg : sigmaGL σ g = g) : ∃ y : GL (Fin n) k, incl y = g := by
  have hfix : ∀ x : E, σ x = x → ∃ a : k, algebraMap k E a = x := by
    intro x hx
    have hσ : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact hx
    have hall : ∀ τ : E ≃ₐ[k] E, τ x = x := by
      intro τ
      have := (Subgroup.zpowers_le.mpr hσ) (hgen τ)
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    have := (IsGalois.mem_bot_iff_fixed x).mpr hall
    rwa [IntermediateField.mem_bot] at this
  have hent : ∀ (h : GL (Fin n) E), sigmaGL σ h = h → ∀ i j,
      σ ((h : Matrix (Fin n) (Fin n) E) i j) = (h : Matrix (Fin n) (Fin n) E) i j := by
    intro h hh i j
    have := congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E) i j) hh
    exact this
  have hg' : sigmaGL σ g⁻¹ = g⁻¹ := by rw [map_inv, hg]
  choose A hA using fun i j => hfix _ (hent g hg i j)
  choose B hB using fun i j => hfix _ (hent g⁻¹ hg' i j)
  have hinj : Function.Injective (algebraMap k E) := (algebraMap k E).injective
  have hAm : (Matrix.of A).map (algebraMap k E) = (g : Matrix (Fin n) (Fin n) E) := by
    ext i j; exact hA i j
  have hBm : (Matrix.of B).map (algebraMap k E) = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
    ext i j; exact hB i j
  have hAB : Matrix.of A * Matrix.of B = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hAm, hBm, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBA : Matrix.of B * Matrix.of A = 1 := by
    apply Matrix.map_injective hinj
    beta_reduce
    rw [Matrix.map_mul, hAm, hBm, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨Matrix.of A, Matrix.of B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hAm

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Conclude with `σ.commutes _`.
-/
theorem sigmaGL_incl {k E : Type*} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E)
    (y : GL (Fin n) k) : sigmaGL σ (incl y) = incl y := by
  apply Units.ext
  ext i j
  exact σ.commutes _

/- English proof (translation)
Introduce `a b hab`. Apply `Units.ext` to reduce the goal to its premises. Apply `Matrix.map_injective (algebraMap k E).injective` to reduce the goal to its premises. Conclude with `congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E)) hab`.
-/
theorem incl_injective {k E : Type*} [Field k] [Field E] [Algebra k E] :
    Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := by
  intro a b hab
  apply Units.ext
  apply Matrix.map_injective (algebraMap k E).injective
  exact congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E)) hab

/- English proof (translation)
Introduce `hD _ k E _ _ _ _ _ _ _ _ _ _ _ _ hur σ hgen n γ c _ hpc hqc hN`. Take `⟨p, hp, hpi⟩` from `hpc`. Take `⟨q, hq, hqi⟩` from `hqc`. Establish `hσℓ : σ ^ Module.finrank k E = 1`. Rewrite using `[← IsGalois.card_aut_eq_finrank]`.

Conclude with `pow_card_eq_one'`. Establish `hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1`. Rewrite using `[← sigmaGL_pow, hσℓ, sigmaGL_one]`. Establish `hstab : ∀ x ∈ unitGL (n` using `Fin n) E, sigmaGL σ x ∈ unitGL (n := Fin n) E := fun x hx => ((hD k E hur σ hgen).2.2.2.1 σ n x).2 hx`. Establish `hNc : twNorm (sigmaGL σ) (Module.finrank k E) c = incl γ` using `hN`.

Establish `hq' : (((c⁻¹)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p` using `by rw [inv_inv]; exact hp`. Use `⟨fun g => ⟨fun hu => ?_, fun h => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hγ : g⁻¹ * incl γ * g ∈ unitGL (n` using `Fin n) E := by`. Use `twNorm_mem (sigmaGL σ) _ hstab hu (Module.finrank k E)` as an intermediate fact. Rewrite `this` using `[twNorm_twConj_of_pow_eq_one _ hθ, hNc]`. Then use the resulting hypothesis.

Use `⟨?_, hγ⟩` and prove the remaining obligations. Establish `hcg : g⁻¹ * c⁻¹ * g ∈ unitGL (n` using `Fin n) E := conj_mem_unitGL hq hqi hq' hpi hγ`. Establish `he : g⁻¹ * sigmaGL σ g = (g⁻¹ * c⁻¹ * g) * twConj (sigmaGL σ) g c`. Simplify using `only [twConj]`. Use `group`.

Rewrite using `[he]`. Conclude with `mul_mem hcg hu`. Establish `hcg : g⁻¹ * c * g ∈ unitGL (n` using `Fin n) E := conj_mem_unitGL hp hpi hq hqi h.2`. Establish `he : twConj (sigmaGL σ) g c = (g⁻¹ * c * g) * (g⁻¹ * sigmaGL σ g)`. Simplify using `only [twConj]`.

Use `group`. Rewrite using `[he]`. Conclude with `mul_mem hcg h.1`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce `hg`. Establish `hcomm` using `twCent_commute_twNorm (sigmaGL σ) hθ c hg`. Rewrite `hcomm` using `[hNc]`. Establish `hcg : g⁻¹ * c * g = c` using `conj_eq_of_commute hp hcomm`. Establish `hg' : g⁻¹ * c * sigmaGL σ g = c` using `hg`.

Establish `hfix : sigmaGL σ g = g`. Establish `h1 : g⁻¹ * c * sigmaGL σ g = g⁻¹ * c * g` using `by rw [hg', hcg]`. Conclude with `mul_left_cancel h1`. Take `⟨y, rfl⟩` from `exists_incl_of_fixed σ hgen g hfix`. Use `⟨y, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]`. Apply `incl_injective (E := E)` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul]`. Conclude with `hcomm`. Introduce and unpack `⟨y, hy, rfl⟩`.

Rewrite `hy` using `[SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]`. Establish `hcomm : incl y * incl γ = (incl γ : GL (Fin n) E) * incl y`. Rewrite using `[← map_mul, ← map_mul, hy]`. Establish `hcg` using `conj_eq_of_commute hp hcomm`. Use `show (incl y)⁻¹ * c * sigmaGL σ (incl y) = c`.

Rewrite using `[sigmaGL_incl, hcg]`.
-/
theorem cstable_iff_and_twCent : D0a → A1 → L4 := by
  intro hD _ k E _ _ _ _ _ _ _ _ _ _ _ _ hur σ hgen n γ c _ hpc hqc hN
  obtain ⟨p, hp, hpi⟩ := hpc
  obtain ⟨q, hq, hqi⟩ := hqc
  have hσℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hσℓ, sigmaGL_one]
  have hstab : ∀ x ∈ unitGL (n := Fin n) E, sigmaGL σ x ∈ unitGL (n := Fin n) E :=
    fun x hx => ((hD k E hur σ hgen).2.2.2.1 σ n x).2 hx
  have hNc : twNorm (sigmaGL σ) (Module.finrank k E) c = incl γ := hN
  have hq' : (((c⁻¹)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p := by rw [inv_inv]; exact hp
  refine ⟨fun g => ⟨fun hu => ?_, fun h => ?_⟩, ?_⟩
  · have hγ : g⁻¹ * incl γ * g ∈ unitGL (n := Fin n) E := by
      have := twNorm_mem (sigmaGL σ) _ hstab hu (Module.finrank k E)
      rwa [twNorm_twConj_of_pow_eq_one _ hθ, hNc] at this
    refine ⟨?_, hγ⟩
    have hcg : g⁻¹ * c⁻¹ * g ∈ unitGL (n := Fin n) E := conj_mem_unitGL hq hqi hq' hpi hγ
    have he : g⁻¹ * sigmaGL σ g = (g⁻¹ * c⁻¹ * g) * twConj (sigmaGL σ) g c := by
      simp only [twConj]; group
    rw [he]
    exact mul_mem hcg hu
  · have hcg : g⁻¹ * c * g ∈ unitGL (n := Fin n) E := conj_mem_unitGL hp hpi hq hqi h.2
    have he : twConj (sigmaGL σ) g c = (g⁻¹ * c * g) * (g⁻¹ * sigmaGL σ g) := by
      simp only [twConj]; group
    rw [he]
    exact mul_mem hcg h.1
  · ext g
    constructor
    · intro hg
      have hcomm := twCent_commute_twNorm (sigmaGL σ) hθ c hg
      rw [hNc] at hcomm
      have hcg : g⁻¹ * c * g = c := conj_eq_of_commute hp hcomm
      have hg' : g⁻¹ * c * sigmaGL σ g = c := hg
      have hfix : sigmaGL σ g = g := by
        have h1 : g⁻¹ * c * sigmaGL σ g = g⁻¹ * c * g := by rw [hg', hcg]
        exact mul_left_cancel h1
      obtain ⟨y, rfl⟩ := exists_incl_of_fixed σ hgen g hfix
      refine ⟨y, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply incl_injective (E := E)
      rw [map_mul, map_mul]
      exact hcomm
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
      have hcomm : incl y * incl γ = (incl γ : GL (Fin n) E) * incl y := by
        rw [← map_mul, ← map_mul, hy]
      have hcg := conj_eq_of_commute hp hcomm
      show (incl y)⁻¹ * c * sigmaGL σ (incl y) = c
      rw [sigmaGL_incl, hcg]

end GlobalTheory.CompanionTheory.UnitLattice
