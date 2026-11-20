import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryCoordinateAlgebraDense
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AutFormDefiniteUnitaryEqSumPolynomialMulAutForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjPolynomialDefiniteUnitaryRational
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.ConjSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def gen (t : (E →+* ℂ) × Fin n × Fin n) : infU E n → ℂ := fun x => (cEmb t.1 x.1).val t.2.1 t.2.2

def mono (l : List ((E →+* ℂ) × Fin n × Fin n)) : infU E n → ℂ := (l.map gen).prod

variable (E n) in

def polys (N : ℕ) : Submodule ℂ (infU E n → ℂ) :=
  Submodule.span ℂ (mono '' {l | l.length ≤ N})

/- English proof (translation)
The claim follows from `FiniteDimensional.span_of_finite ℂ ((List.finite_length_le _ N).image _)`.
-/
theorem polys_fd (N : ℕ) : FiniteDimensional ℂ (polys E n N) :=
  FiniteDimensional.span_of_finite ℂ ((List.finite_length_le _ N).image _)

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun _ hl => le_trans hl h)`.
-/
theorem polys_mono {N N' : ℕ} (h : N ≤ N') : polys E n N ≤ polys E n N' :=
  Submodule.span_mono (Set.image_mono fun _ hl => le_trans hl h)

variable (E n) in

abbrev gens : Set (infU E n → ℂ) := {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}

/- English proof (translation)
Proceed by induction on `hf using Submonoid.closure_induction with`. Consider the case `mem f hf`. Take `⟨τ, i, j, rfl⟩` from `hf`. Conclude with `⟨[(τ, i, j)], by funext x; simp [mono, gen]⟩`. Consider the case `one => exact ⟨[], by simp [mono]⟩`.

Consider the case `mul f g _ _ hf hg`. Take `⟨l, rfl⟩` from `hf`. Take `⟨l', rfl⟩` from `hg`. Conclude with `⟨l ++ l', by simp [mono]⟩`.
-/
theorem exists_mono_of_mem_closure {f : infU E n → ℂ} (hf : f ∈ Submonoid.closure (gens E n)) :
    ∃ l, f = mono l := by
  induction hf using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ := hf
    exact ⟨[(τ, i, j)], by funext x; simp [mono, gen]⟩
  | one => exact ⟨[], by simp [mono]⟩
  | mul f g _ _ hf hg =>
    obtain ⟨l, rfl⟩ := hf
    obtain ⟨l', rfl⟩ := hg
    exact ⟨l ++ l', by simp [mono]⟩

/- English proof (translation)
Establish `h : p ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (gens E n))` using `hp`. Rewrite `h` using `[Algebra.adjoin_eq_span]`. Use `clear hp`. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem f hf`.

Take `⟨l, rfl⟩` from `exists_mono_of_mem_closure hf`. Conclude with `⟨l.length, Submodule.subset_span ⟨l, (le_refl l.length : l.length ≤ l.length), rfl⟩⟩`. Consider the case `zero => exact ⟨0, zero_mem _⟩`. Consider the case `add f g _ _ hf hg`. Take `⟨N, hN⟩` from `hf`.

Take `⟨N', hN'⟩` from `hg`. Conclude with `⟨max N N', add_mem (polys_mono (le_max_left _ _) hN) (polys_mono (le_max_right _ _) hN')⟩`. Consider the case `smul c f _ hf`. Take `⟨N, hN⟩` from `hf`. Conclude with `⟨N, Submodule.smul_mem _ c hN⟩`.
-/
theorem exists_polys_of_mem_adjoin {p : infU E n → ℂ} (hp : p ∈ Algebra.adjoin ℂ (gens E n)) :
    ∃ N, p ∈ polys E n N := by
  have h : p ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (gens E n)) := hp
  rw [Algebra.adjoin_eq_span] at h
  clear hp
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := exists_mono_of_mem_closure hf
    exact ⟨l.length, Submodule.subset_span ⟨l, (le_refl l.length : l.length ≤ l.length), rfl⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add f g _ _ hf hg =>
    obtain ⟨N, hN⟩ := hf
    obtain ⟨N', hN'⟩ := hg
    exact ⟨max N N', add_mem (polys_mono (le_max_left _ _) hN) (polys_mono (le_max_right _ _) hN')⟩
  | smul c f _ hf =>
    obtain ⟨N, hN⟩ := hf
    exact ⟨N, Submodule.smul_mem _ c hN⟩

/- English proof (translation)
Unfold `mono`. Proceed by induction on `l with`. Consider the case `nil => simpa using one_mem (Algebra.adjoin ℂ (gens E n))`. Consider the case `cons t l ih`. Rewrite using `[List.map_cons, List.prod_cons]`.

Conclude with `mul_mem (Algebra.subset_adjoin ⟨t.1, t.2.1, t.2.2, rfl⟩) ih`.
-/
theorem mono_mem_adjoin (l : List ((E →+* ℂ) × Fin n × Fin n)) : mono l ∈ Algebra.adjoin ℂ (gens E n) := by
  unfold mono
  induction l with
  | nil => simpa using one_mem (Algebra.adjoin ℂ (gens E n))
  | cons t l ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (Algebra.subset_adjoin ⟨t.1, t.2.1, t.2.2, rfl⟩) ih

/- English proof (translation)
The claim follows from `Submodule.span_le.2 (by rintro _ ⟨l, -, rfl⟩; exact mono_mem_adjoin l)`.
-/
theorem polys_le_adjoin (N : ℕ) : polys E n N ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (gens E n)) :=
  Submodule.span_le.2 (by rintro _ ⟨l, -, rfl⟩; exact mono_mem_adjoin l)

def conjIdx (σ : ℂ ≃+* ℂ) (t : (E →+* ℂ) × Fin n × Fin n) : (E →+* ℂ) × Fin n × Fin n :=
  (σ.toRingHom.comp t.1, t.2)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [mono]`. Consider the case `cons t l ih`. Simplify using `only [mono, List.map_cons, List.prod_cons, Pi.mul_apply] at ih ⊢`. Rewrite using `[ih, map_mul]`.

Use `congr 1`. Take `⟨x, hx⟩` from `exists_cEmb_entry_eq hγ hk t.2.1 t.2.2`. Simplify using `only [gen, conjIdx, hx]`. Both sides reduce to the same expression.
-/
theorem mono_conj (σ : ℂ ≃+* ℂ) (l : List ((E →+* ℂ) × Fin n × Fin n)) {γ : UA E n} (hγ : γ ∈ ratU E n)
    (k : infU E n) (hk : cInf k.1 = cInf γ) : mono (l.map (conjIdx σ)) k = σ (mono l k) := by
  induction l with
  | nil => simp [mono]
  | cons t l ih =>
    simp only [mono, List.map_cons, List.prod_cons, Pi.mul_apply] at ih ⊢
    rw [ih, map_mul]
    congr 1
    obtain ⟨x, hx⟩ := exists_cEmb_entry_eq hγ hk t.2.1 t.2.2
    simp only [gen, conjIdx, hx]
    rfl

/- English proof (translation)
Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨l, hl, rfl⟩` from `hf`. Conclude with `⟨mono (l.map (conjIdx σ)), Submodule.subset_span ⟨_, by simpa using hl, rfl⟩, fun γ hγ k hk => mono_conj σ l hγ k hk⟩`. Consider the case `zero => exact ⟨0, zero_mem _, fun _ _ _ _ => by simp⟩`.

Consider the case `add f g _ _ hf hg`. Take `⟨f', hf', hf⟩` from `hf`. Take `⟨g', hg', hg⟩` from `hg`. Conclude with `⟨f' + g', add_mem hf' hg', fun γ hγ k hk => by`. Rewrite using `[Pi.add_apply, Pi.add_apply, map_add, hf γ hγ k hk, hg γ hγ k hk]⟩`.

Consider the case `smul c f _ hf`. Take `⟨f', hf', hf⟩` from `hf`. Conclude with `⟨σ c • f', Submodule.smul_mem _ _ hf', fun γ hγ k hk => by`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hf γ hγ k hk]⟩`.
-/
theorem exists_conj_polys (σ : ℂ ≃+* ℂ) {N : ℕ} {p : infU E n → ℂ} (hp : p ∈ polys E n N) :
    ∃ p' ∈ polys E n N, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  induction hp using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, hl, rfl⟩ := hf
    exact ⟨mono (l.map (conjIdx σ)), Submodule.subset_span ⟨_, by simpa using hl, rfl⟩,
      fun γ hγ k hk => mono_conj σ l hγ k hk⟩
  | zero => exact ⟨0, zero_mem _, fun _ _ _ _ => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    exact ⟨f' + g', add_mem hf' hg', fun γ hγ k hk => by
      rw [Pi.add_apply, Pi.add_apply, map_add, hf γ hγ k hk, hg γ hγ k hk]⟩
  | smul c f _ hf =>
    obtain ⟨f', hf', hf⟩ := hf
    exact ⟨σ c • f', Submodule.smul_mem _ _ hf', fun γ hγ k hk => by
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hf γ hγ k hk]⟩

/- English proof (translation)
Introduce `E _ _ _ n φ hφ`. Take `⟨hdense, hdk, -, a, b, -, -, hab, -⟩` from `GlobalTheory.UnitarySplit.dense_and_split E n`. Take `⟨m, p, e, hpe, hdec⟩` from `GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm E n φ hφ`. Establish `hcont` using `(GlobalTheory.PolyRealU.poly_infU E n).1`. Use `choose D hD using fun i => exists_polys_of_mem_adjoin (hpe i).1`.

Use `set N := Finset.univ.sup D with hN`. Establish `hpN : ∀ i, p i ∈ polys E n N` using `fun i => polys_mono (Finset.le_sup (Finset.mem_univ i)) (hD i)`. Use `set K := GlobalTheory.UnitaryDecomp.finStab φ with hK`. Take `⟨S, hS⟩` from `GlobalTheory.DefU.ClassFin.classSet_finite E n K hφ.level`. Use `set S' : Finset (UA E n) := S.image fun s => ((a s : finU E n) : UA E n) with hS'`.

Set `M : Submodule ℂ (UA E n → ℂ)` to `{ carrier := {ψ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ K, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ s ∈ S', (fun x : infU E n => ψ (s * x)) ∈ polys E n N} add_mem' := fun {ψ χ} hψ hχ => ⟨fun γ hγ g => by simp only [Pi.add_apply, hψ.1 γ hγ g, hχ.1 γ hγ g], fun k hk g => by s …`. Establish `hred : ∀ g : UA E n, ∃ s ∈ S', ∃ y : infU E n, ∀ ψ ∈ M, ψ g = ψ (s * y)`. Introduce `g`. Take `⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩` from `hS g`. Use `⟨((a s : finU E n) : UA E n), by rw [hS']; exact Finset.mem_image_of_mem _ hs, ⟨(b s).1 * x, mul_mem (b s).2 hx⟩, fun ψ hψ => ?_⟩` and prove the remaining obligations.

Rewrite using `[hψ.2.1 k hk, mul_assoc, hψ.1 γ hγ]`. Use `conv_lhs => rw [hab s]`. Simplify using `only [mul_assoc]`. Use `haveI := polys_fd (E := E) (n := n) N`. Set `f : M →ₗ[ℂ] ((s : S') → polys E n N)` to `{ toFun := fun ψ s => ⟨fun x => ψ.1 (s.1 * x), ψ.2.2.2 s.1 s.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`.

Establish `hinj : Function.Injective f`. Introduce `ψ χ h`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Take `⟨s, hs, y, hy⟩` from `hred g`. Rewrite using `[hy ψ.1 ψ.2, hy χ.1 χ.2]`.

Conclude with `congrFun (congrArg Subtype.val (congrFun h ⟨s, hs⟩)) y`. Use `⟨M, Module.Finite.of_injective f hinj, fun σ φ' hφ' hagree => ?_⟩` and prove the remaining obligations. Establish `hrat : ∀ s ∈ finU E n, ∀ k : infU E n, ∀ γ ∈ ratU E n, cInf k.1 = cInf γ → φ' (s * (k : UA E n)) = σ (φ (s * (k : UA E n)))`. Introduce `s hs k γ hγ hk`. Establish `hy : γ⁻¹ * (s * (k : UA E n)) ∈ finU E n`.

Establish `hs1 : cInf s = 1` using `hs`. Use `show cInf (γ⁻¹ * (s * (k : UA E n))) = 1`. Rewrite using `[map_mul, map_mul, map_inv, hs1, hk, one_mul, inv_mul_cancel]`. Establish `e1 : s * (k : UA E n) = γ * (γ⁻¹ * (s * (k : UA E n)))` using `by group`. Rewrite using `[e1, hφ'.left γ hγ, hφ.left γ hγ, hagree _ hy]`.

Use `⟨hφ'.left, fun k hk => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Establish `hkφ : ∀ x, φ (x * (k : UA E n)) = φ x` using `fun x => congrFun hk x`. Use `congrFun (Continuous.ext_on hdense (hφ'.cont.comp (continuous_mul_const _)) hφ'.cont ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨γ, hγ, x, hx, rfl⟩`. Establish `hxk : x * (k : UA E n) ∈ finU E n` using `mul_mem hx k.2`.

Simplify using `only [Function.comp_apply]`. Rewrite using `[mul_assoc, hφ'.left γ hγ, hφ'.left γ hγ, hagree _ hxk, hagree _ hx, hkφ]`. Take `⟨s₀, hs₀, rfl⟩` from `Finset.mem_image.1 hs`. Establish `hsf : ((a s₀ : finU E n) : UA E n) ∈ finU E n` using `(a s₀).2`. Use `choose p' hp'm hp' using fun i => exists_conj_polys σ (hpN i)`.

Establish `hq : (∑ i, σ (e i (a s₀)) • p' i) ∈ polys E n N` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hp'm i)`. Use `hq using 1` and compare the differences between its conclusion and the goal. Use `Continuous.ext_on hdk (hφ'.cont.comp (continuous_const.mul continuous_subtype_val)) (hcont _ (polys_le_adjoin N hq)) ?_` and prove the remaining obligations. Introduce and unpack `k ⟨γ, hγ, hk⟩`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[hrat _ hsf k γ hγ hk, hdec k, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hp' i γ hγ k hk, mul_comm]`.
-/
theorem conj_span_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ),
    IsAutFormU φ → ∃ M : Submodule ℂ (UA E n → ℂ), FiniteDimensional ℂ M ∧ ∀ (σ : ℂ ≃+* ℂ) (φ' : UA E n → ℂ),
      IsAutFormU φ' → (∀ g ∈ finU E n, φ' g = σ (φ g)) → φ' ∈ M := by
  intro E _ _ _ n φ hφ
  classical
  obtain ⟨hdense, hdk, -, a, b, -, -, hab, -⟩ := GlobalTheory.UnitarySplit.dense_and_split E n
  obtain ⟨m, p, e, hpe, hdec⟩ := GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm E n φ hφ
  have hcont := (GlobalTheory.PolyRealU.poly_infU E n).1
  choose D hD using fun i => exists_polys_of_mem_adjoin (hpe i).1
  set N := Finset.univ.sup D with hN
  have hpN : ∀ i, p i ∈ polys E n N := fun i => polys_mono (Finset.le_sup (Finset.mem_univ i)) (hD i)
  set K := GlobalTheory.UnitaryDecomp.finStab φ with hK
  obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hφ.level
  set S' : Finset (UA E n) := S.image fun s => ((a s : finU E n) : UA E n) with hS'
  let M : Submodule ℂ (UA E n → ℂ) :=
    { carrier := {ψ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ K, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧
        ∀ s ∈ S', (fun x : infU E n => ψ (s * x)) ∈ polys E n N}
      add_mem' := fun {ψ χ} hψ hχ =>
        ⟨fun γ hγ g => by simp only [Pi.add_apply, hψ.1 γ hγ g, hχ.1 γ hγ g],
          fun k hk g => by simp only [Pi.add_apply, hψ.2.1 k hk g, hχ.2.1 k hk g],
          fun s hs => add_mem (hψ.2.2 s hs) (hχ.2.2 s hs)⟩
      zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => zero_mem _⟩
      smul_mem' := fun c ψ hψ =>
        ⟨fun γ hγ g => by simp only [Pi.smul_apply, hψ.1 γ hγ g],
          fun k hk g => by simp only [Pi.smul_apply, hψ.2.1 k hk g],
          fun s hs => Submodule.smul_mem _ c (hψ.2.2 s hs)⟩ }

  have hred : ∀ g : UA E n, ∃ s ∈ S', ∃ y : infU E n, ∀ ψ ∈ M, ψ g = ψ (s * y) := by
    intro g
    obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
    refine ⟨((a s : finU E n) : UA E n), by rw [hS']; exact Finset.mem_image_of_mem _ hs, ⟨(b s).1 * x, mul_mem (b s).2 hx⟩, fun ψ hψ => ?_⟩
    rw [hψ.2.1 k hk, mul_assoc, hψ.1 γ hγ]
    conv_lhs => rw [hab s]
    simp only [mul_assoc]
  haveI := polys_fd (E := E) (n := n) N
  let f : M →ₗ[ℂ] ((s : S') → polys E n N) :=
    { toFun := fun ψ s => ⟨fun x => ψ.1 (s.1 * x), ψ.2.2.2 s.1 s.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective f := by
    intro ψ χ h
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨s, hs, y, hy⟩ := hred g
    rw [hy ψ.1 ψ.2, hy χ.1 χ.2]
    exact congrFun (congrArg Subtype.val (congrFun h ⟨s, hs⟩)) y
  refine ⟨M, Module.Finite.of_injective f hinj, fun σ φ' hφ' hagree => ?_⟩

  have hrat : ∀ s ∈ finU E n, ∀ k : infU E n, ∀ γ ∈ ratU E n, cInf k.1 = cInf γ →
      φ' (s * (k : UA E n)) = σ (φ (s * (k : UA E n))) := by
    intro s hs k γ hγ hk
    have hy : γ⁻¹ * (s * (k : UA E n)) ∈ finU E n := by
      have hs1 : cInf s = 1 := hs
      show cInf (γ⁻¹ * (s * (k : UA E n))) = 1
      rw [map_mul, map_mul, map_inv, hs1, hk, one_mul, inv_mul_cancel]
    have e1 : s * (k : UA E n) = γ * (γ⁻¹ * (s * (k : UA E n))) := by group
    rw [e1, hφ'.left γ hγ, hφ.left γ hγ, hagree _ hy]
  refine ⟨hφ'.left, fun k hk => ?_, fun s hs => ?_⟩
  ·
    have hkφ : ∀ x, φ (x * (k : UA E n)) = φ x := fun x => congrFun hk x
    refine congrFun (Continuous.ext_on hdense (hφ'.cont.comp (continuous_mul_const _)) hφ'.cont ?_)
    rintro _ ⟨γ, hγ, x, hx, rfl⟩
    have hxk : x * (k : UA E n) ∈ finU E n := mul_mem hx k.2
    simp only [Function.comp_apply]
    rw [mul_assoc, hφ'.left γ hγ, hφ'.left γ hγ, hagree _ hxk, hagree _ hx, hkφ]
  · obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.1 hs
    have hsf : ((a s₀ : finU E n) : UA E n) ∈ finU E n := (a s₀).2
    choose p' hp'm hp' using fun i => exists_conj_polys σ (hpN i)
    have hq : (∑ i, σ (e i (a s₀)) • p' i) ∈ polys E n N :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hp'm i)
    convert hq using 1
    refine Continuous.ext_on hdk (hφ'.cont.comp (continuous_const.mul continuous_subtype_val))
      (hcont _ (polys_le_adjoin N hq)) ?_
    rintro k ⟨γ, hγ, hk⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hrat _ hsf k γ hγ hk, hdec k, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hp' i γ hγ k hk, mul_comm]

end GlobalTheory.ConjSpan

end
