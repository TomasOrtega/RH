import Formalism.CharacterColumnKernels.StatementMF
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero

open Module IsDiscreteValuationRing

noncomputable section

namespace Formalism.NG

namespace IdempotentImageSmul

section Adj

variable {O OO M Q : Type*} [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup M] [Module OO M]
    [Module O M] [IsScalarTower O OO M] [AddCommGroup Q] [Module O Q] (ε : OO)

def epsE : epsIdeal O ε := ⟨ε, LinearMap.mem_range.mpr ⟨1, by simp⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma dual_smul_apply (a : OO) (φ : EpsDual O OO Q ε) (x : epsIdeal O ε) :
    (a • φ) x = φ (rightMulEps O ε a x) := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show x.1 * algebraMap O OO c = c • x.1`. Rewrite using `[Algebra.smul_def, Algebra.commutes]`.
-/
lemma rightMulEps_algebraMap (c : O) (x : epsIdeal O ε) :
    rightMulEps O ε (algebraMap O OO c) x = c • x := by
  apply Subtype.ext
  show x.1 * algebraMap O OO c = c • x.1
  rw [Algebra.smul_def, Algebra.commutes]

variable {ε}

/- English proof (translation)
Take `⟨y, hy⟩` from `x.2`. Simplify using `only [LinearMap.mulLeft_apply] at hy`. Rewrite using `[← hy, ← mul_assoc, hε.eq]`.
-/
lemma eps_mul_of_mem (hε : IsIdempotentElem ε) (x : epsIdeal O ε) : ε * x.1 = x.1 := by
  obtain ⟨y, hy⟩ := x.2
  simp only [LinearMap.mulLeft_apply] at hy
  rw [← hy, ← mul_assoc, hε.eq]

/- English proof (translation)
Take `⟨y, hy⟩` from `x.2`. Simplify using `only [LinearMap.mulLeft_apply] at hy`. Use `⟨y • m, ?_⟩` and prove the remaining obligations. Use `show ε • (y • m) = x.1 • m`. Rewrite using `[← hy, mul_smul]`.
-/
lemma smul_mem_epsImg (x : epsIdeal O ε) (m : M) : x.1 • m ∈ epsImg O (M := M) ε := by
  obtain ⟨y, hy⟩ := x.2
  simp only [LinearMap.mulLeft_apply] at hy
  refine ⟨y • m, ?_⟩
  show ε • (y • m) = x.1 • m
  rw [← hy, mul_smul]

/- English proof (translation)
Take `⟨z, hz⟩` from `y.2`. Rewrite using `[← hz]`. Use `show ε • ε • z = ε • z`. Rewrite using `[← mul_smul, hε.eq]`.
-/
lemma eps_smul_of_mem (hε : IsIdempotentElem ε) (y : epsImg O (M := M) ε) : ε • y.1 = y.1 := by
  obtain ⟨z, hz⟩ := y.2
  rw [← hz]
  show ε • ε • z = ε • z
  rw [← mul_smul, hε.eq]

variable (ε) [SMulCommClass OO O (EpsDual O OO Q ε)]

def fwd : (M →ₗ[OO] EpsDual O OO Q ε) →ₗ[O] (epsImg O (M := M) ε →ₗ[O] Q) where
  toFun Φ :=
    { toFun := fun y => Φ y.1 (epsE ε)
      map_add' := fun y z => by simp
      map_smul' := fun c y => by
        show Φ (c • y.1) (epsE ε) = c • Φ y.1 (epsE ε)
        rw [← algebraMap_smul OO c y.1, Φ.map_smul, dual_smul_apply, rightMulEps_algebraMap,
          map_smul] }
  map_add' Φ Ψ := rfl
  map_smul' c Φ := rfl

def bwdInner (ψ : epsImg O (M := M) ε →ₗ[O] Q) (m : M) : EpsDual O OO Q ε where
  toFun x := ψ ⟨x.1 • m, smul_mem_epsImg x m⟩
  map_add' x z := by
    rw [← map_add]; congr 1; apply Subtype.ext
    show (x.1 + z.1) • m = x.1 • m + z.1 • m
    rw [add_smul]
  map_smul' c x := by
    rw [← map_smul]; congr 1; apply Subtype.ext
    show (c • x.1) • m = c • (x.1 • m)
    rw [smul_assoc]

def bwd : (epsImg O (M := M) ε →ₗ[O] Q) →ₗ[O] (M →ₗ[OO] EpsDual O OO Q ε) where
  toFun ψ :=
    { toFun := bwdInner ε ψ
      map_add' := fun m m' => by
        apply LinearMap.ext; intro x
        show ψ ⟨x.1 • (m + m'), _⟩ = ψ ⟨x.1 • m, _⟩ + ψ ⟨x.1 • m', _⟩
        rw [← map_add]; congr 1; apply Subtype.ext
        show x.1 • (m + m') = x.1 • m + x.1 • m'
        rw [smul_add]
      map_smul' := fun a m => by
        apply LinearMap.ext; intro x
        show ψ ⟨x.1 • a • m, _⟩ = ψ ⟨(x.1 * a) • m, _⟩
        congr 1; apply Subtype.ext
        show x.1 • a • m = (x.1 * a) • m
        rw [mul_smul] }
  map_add' ψ ψ' := rfl
  map_smul' c ψ := rfl

variable {ε}

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `m`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Use `show Φ (x.1 • m) (epsE ε) = Φ m x`.

Rewrite using `[Φ.map_smul, dual_smul_apply]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ε * x.1 = x.1`. Conclude with `eps_mul_of_mem hε x`.
-/
lemma bwd_fwd (hε : IsIdempotentElem ε) (Φ : M →ₗ[OO] EpsDual O OO Q ε) :
    bwd ε (fwd ε Φ) = Φ := by
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro x
  show Φ (x.1 • m) (epsE ε) = Φ m x
  rw [Φ.map_smul, dual_smul_apply]
  congr 1
  apply Subtype.ext
  show ε * x.1 = x.1
  exact eps_mul_of_mem hε x

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Use `show ψ ⟨ε • y.1, _⟩ = ψ y`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `eps_smul_of_mem hε y`.
-/
lemma fwd_bwd (hε : IsIdempotentElem ε) (ψ : epsImg O (M := M) ε →ₗ[O] Q) :
    fwd ε (bwd ε ψ) = ψ := by
  apply LinearMap.ext
  intro y
  show ψ ⟨ε • y.1, _⟩ = ψ y
  congr 1
  apply Subtype.ext
  exact eps_smul_of_mem hε y

end Adj

section Matlis

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def homQuotEquiv (a : O) :
    ((O ⧸ Ideal.span ({a} : Set O)) →ₗ[O] KO O) ≃ₗ[O]
      LinearMap.ker (matQ O (fun _ _ => a : Matrix Unit Unit O)) where
  toFun φ := ⟨fun _ => φ (Submodule.Quotient.mk 1), by
    rw [LinearMap.mem_ker]; funext i
    show ∑ _j : Unit, a • φ (Submodule.Quotient.mk 1) = 0
    rw [Fintype.sum_unique, ← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
      (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton_self a), map_zero]⟩
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
  invFun v := (Ideal.span ({a} : Set O)).liftQ (LinearMap.toSpanSingleton O _ (v.1 ())) (by
    rw [Ideal.span, Submodule.span_le, Set.singleton_subset_iff]
    show a • v.1 () = 0
    have h : (∑ j : Unit, a • v.1 j) = 0 := congrFun (LinearMap.mem_ker.mp v.2) ()
    rwa [Fintype.sum_unique] at h)
  left_inv φ := by
    apply LinearMap.ext; intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]
      show x • φ (Submodule.Quotient.mk 1) = φ (Submodule.Quotient.mk x)
      rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  right_inv v := by
    apply Subtype.ext; funext i
    show ((Ideal.span ({a} : Set O)).liftQ _ _) (Submodule.Quotient.mk 1) = v.1 i
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]

/- English proof (translation)
Rewrite using `[(homQuotEquiv a).length_eq, lenKer O Unit (fun _ _ => a)]`. Conclude with `congrArg _ (Matrix.det_unique _)`.
-/
lemma length_hom_quot (a : O) :
    Module.length O ((O ⧸ Ideal.span ({a} : Set O)) →ₗ[O] KO O) = addVal O a := by
  rw [(homQuotEquiv a).length_eq, lenKer O Unit (fun _ _ => a)]
  exact congrArg _ (Matrix.det_unique _)

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `hfl : IsFiniteLength O O` using `Module.length_ne_top_iff.mp h`. Rewrite `hfl` using `[isFiniteLength_iff_isNoetherian_isArtinian]`. Use `haveI : IsArtinianRing O := hfl.2`. Conclude with `IsDiscreteValuationRing.not_isField O (IsArtinianRing.isField_of_isDomain O)`.
-/
lemma length_self_top : Module.length O O = ⊤ := by
  by_contra h
  have hfl : IsFiniteLength O O := Module.length_ne_top_iff.mp h
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
  haveI : IsArtinianRing O := hfl.2
  exact IsDiscreteValuationRing.not_isField O (IsArtinianRing.isField_of_isDomain O)

end Matlis

end IdempotentImageSmul

open IdempotentImageSmul

/- English proof (translation)
Introduce `O N _ _ _ _ _ hN`. Establish `hNA` using `isFiniteLength_iff_isNoetherian_isArtinian.mp hN`. Establish `: IsNoetherian O N` using `hNA.1`. Take `⟨n, ι, _, p, -, e, ⟨f⟩⟩` from `Module.equiv_free_prod_directSum (R := O) (M := N)`. Use `set A : ι → Type _ := fun i => O ⧸ O ∙ p i ^ e i with hA`.

Set `g : (DirectSum ι A) ≃ₗ[O] (Π i, A i)` to `DirectSum.linearEquivFunOnFintype O ι A`. Establish `hlenA : ∀ i, Module.length O (A i) = addVal O (p i ^ e i)` using `fun i => IdempotentNormalFormsLenFacts.length_quot_span (p i ^ e i)`. Establish `hlenH : ∀ i, Module.length O (A i →ₗ[O] KO O) = addVal O (p i ^ e i)` using `fun i => length_hom_quot (p i ^ e i)`. Establish `hN1 : Module.length O N = Module.length O (Fin n →₀ O) + ∑ i, addVal O (p i ^ e i)`. Rewrite using `[f.length_eq, Module.length_prod, g.length_eq, Module.length_pi_of_fintype]`.

Simplify using `only [hlenA]`. Establish `hF : Module.length O (Fin n →₀ O) = 0`. Rewrite using `[Module.length_finsupp, length_self_top]`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality.

Simplify using the standard rewrite rules. It suffices to derive a contradiction. Establish `: Module.length O N = ⊤`. Rewrite using `[hN1, Module.length_finsupp, length_self_top, ENat.card_eq_coe_fintype_card, Fintype.card_fin, ENat.mul_top (by exact_mod_cast hn.ne'), top_add]`. Conclude with `(Module.length_ne_top_iff.mpr hN) this`.

Establish `: Subsingleton (Fin n →₀ O)` using `Module.length_eq_zero_iff.mp hF`. Establish `hFH : Module.length O ((Fin n →₀ O) →ₗ[O] KO O) = 0`. Rewrite using `[Module.length_eq_zero_iff]`. Conclude with `⟨fun φ ψ => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩`. Set `h1 : (N →ₗ[O] KO O) ≃ₗ[O] ((Fin n →₀ O) × DirectSum ι A →ₗ[O] KO O)` to `f.arrowCongr (LinearEquiv.refl O (KO O))`.

Set `h2 : (DirectSum ι A →ₗ[O] KO O) ≃ₗ[O] ((Π i, A i) →ₗ[O] KO O)` to `g.arrowCongr (LinearEquiv.refl O (KO O))`. Establish `h3 : Module.length O ((Π i, A i) →ₗ[O] KO O) = ∑ i, addVal O (p i ^ e i)`. Use `(LinearMap.lsum O A O : (Π i, A i →ₗ[O] KO O) ≃ₗ[O] _).length_eq` as an intermediate fact. Rewrite using `[← this, Module.length_pi_of_fintype]`. Simplify using `only [hlenH]`.

Rewrite using `[h1.length_eq, ← (LinearMap.coprodEquiv O).length_eq, Module.length_prod, h2.length_eq, h3, hFH, hN1, hF]`.
-/
theorem matlis : StatMatlis := by
  classical
  intro O N _ _ _ _ _ hN
  have hNA := isFiniteLength_iff_isNoetherian_isArtinian.mp hN
  have : IsNoetherian O N := hNA.1
  obtain ⟨n, ι, _, p, -, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum (R := O) (M := N)
  set A : ι → Type _ := fun i => O ⧸ O ∙ p i ^ e i with hA
  let g : (DirectSum ι A) ≃ₗ[O] (Π i, A i) := DirectSum.linearEquivFunOnFintype O ι A
  have hlenA : ∀ i, Module.length O (A i) = addVal O (p i ^ e i) := fun i =>
    IdempotentNormalFormsLenFacts.length_quot_span (p i ^ e i)
  have hlenH : ∀ i, Module.length O (A i →ₗ[O] KO O) = addVal O (p i ^ e i) := fun i =>
    length_hom_quot (p i ^ e i)
  have hN1 : Module.length O N =
      Module.length O (Fin n →₀ O) + ∑ i, addVal O (p i ^ e i) := by
    rw [f.length_eq, Module.length_prod, g.length_eq, Module.length_pi_of_fintype]
    simp only [hlenA]
  have hF : Module.length O (Fin n →₀ O) = 0 := by
    rw [Module.length_finsupp, length_self_top]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exfalso
      have : Module.length O N = ⊤ := by
        rw [hN1, Module.length_finsupp, length_self_top, ENat.card_eq_coe_fintype_card,
          Fintype.card_fin, ENat.mul_top (by exact_mod_cast hn.ne'), top_add]
      exact (Module.length_ne_top_iff.mpr hN) this
  have : Subsingleton (Fin n →₀ O) := Module.length_eq_zero_iff.mp hF
  have hFH : Module.length O ((Fin n →₀ O) →ₗ[O] KO O) = 0 := by
    rw [Module.length_eq_zero_iff]
    exact ⟨fun φ ψ => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  let h1 : (N →ₗ[O] KO O) ≃ₗ[O] ((Fin n →₀ O) × DirectSum ι A →ₗ[O] KO O) :=
    f.arrowCongr (LinearEquiv.refl O (KO O))
  let h2 : (DirectSum ι A →ₗ[O] KO O) ≃ₗ[O] ((Π i, A i) →ₗ[O] KO O) :=
    g.arrowCongr (LinearEquiv.refl O (KO O))
  have h3 : Module.length O ((Π i, A i) →ₗ[O] KO O) = ∑ i, addVal O (p i ^ e i) := by
    have := (LinearMap.lsum O A O : (Π i, A i →ₗ[O] KO O) ≃ₗ[O] _).length_eq
    rw [← this, Module.length_pi_of_fintype]
    simp only [hlenH]
  rw [h1.length_eq, ← (LinearMap.coprodEquiv O).length_eq, Module.length_prod, h2.length_eq,
    h3, hFH, hN1, hF]

end Formalism.NG
